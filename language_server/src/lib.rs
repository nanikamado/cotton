#[cfg(test)]
mod tests;

use compiler::{
    FxHashMap, OpPrecedenceMap, PrintTypeOfGlobalVariableForUser,
    PrintTypeOfLocalVariableForUser, Token, TokenId, TokenKind,
    TokenMapWithEnv,
};
use dashmap::DashMap;
use once_cell::sync::Lazy;
use std::collections::HashMap;
use std::fs;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

type HoverMap = Vec<Vec<Option<Hover>>>;

#[derive(Debug, PartialEq, Eq)]
enum TokenCache {
    Cached(SemanticTokens, HoverMap),
    Changed,
}

#[derive(Debug)]
struct Backend {
    client: Client,
    tokens: DashMap<Url, TokenCache>,
}

const SUPPORTED_TYPES: &[SemanticTokenType] = &[
    SemanticTokenType::STRING,
    SemanticTokenType::NUMBER,
    SemanticTokenType::TYPE,
    SemanticTokenType::new("constructor"),
    SemanticTokenType::INTERFACE,
    SemanticTokenType::FUNCTION,
    SemanticTokenType::VARIABLE,
    SemanticTokenType::KEYWORD,
    SemanticTokenType::COMMENT,
    SemanticTokenType::OPERATOR,
    SemanticTokenType::new("constructorOperator"),
];

static SUPPORTED_TYPE_MAP: Lazy<HashMap<&'static SemanticTokenType, u32>> =
    Lazy::new(|| {
        SUPPORTED_TYPES
            .iter()
            .enumerate()
            .map(|(i, t)| (t, i as u32))
            .collect()
    });

#[tower_lsp::async_trait]
impl LanguageServer for Backend {
    async fn initialize(
        &self,
        _: InitializeParams,
    ) -> Result<InitializeResult> {
        self.client
            .log_message(MessageType::INFO, "initializing")
            .await;
        Ok(InitializeResult {
            server_info: None,
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    TextDocumentSyncKind::INCREMENTAL,
                )),
                semantic_tokens_provider: Some(
                    SemanticTokensOptions {
                        legend: SemanticTokensLegend {
                            token_types: SUPPORTED_TYPES.to_vec(),
                            token_modifiers: Vec::new(),
                        },
                        full: Some(SemanticTokensFullOptions::Bool(true)),
                        range: None,
                        ..Default::default()
                    }
                    .into(),
                ),
                hover_provider: Some(HoverProviderCapability::Simple(true)),
                ..ServerCapabilities::default()
            },
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        self.client
            .log_message(MessageType::INFO, "initialized")
            .await;
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    async fn did_change_configuration(&self, _: DidChangeConfigurationParams) {
        self.client
            .log_message(MessageType::INFO, "configuration changed")
            .await;
    }

    async fn did_change_watched_files(&self, _: DidChangeWatchedFilesParams) {
        self.client
            .log_message(MessageType::INFO, "watched files changed")
            .await;
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        self.client
            .log_message(
                MessageType::INFO,
                &format!("opend {}.", params.text_document.uri),
            )
            .await;
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        self.client
            .log_message(
                MessageType::INFO,
                &format!("changed {}", params.text_document.uri),
            )
            .await;
        self.tokens
            .insert(params.text_document.uri, TokenCache::Changed);
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        self.client
            .log_message(MessageType::INFO, "file saved.")
            .await;
        if let Some(r) = self.tokens.get(&params.text_document.uri) {
            self.client
                .log_message(MessageType::INFO, "document found")
                .await;
            let changed = r.value() == &TokenCache::Changed;
            drop(r);
            if changed {
                self.tokens.remove(&params.text_document.uri);
                self.client
                    .log_message(MessageType::INFO, "removed `changed`.")
                    .await;
                self.client.semantic_tokens_refresh().await.unwrap();
                self.client
                    .log_message(
                        MessageType::INFO,
                        "requested `semantic_tokens_refresh`.",
                    )
                    .await;
            } else {
                self.client
                    .log_message(MessageType::INFO, "already cached.")
                    .await;
            }
        } else {
            self.client
                .log_message(MessageType::INFO, "not cached yet.")
                .await;
        }
    }

    async fn did_close(&self, _: DidCloseTextDocumentParams) {
        self.client
            .log_message(MessageType::INFO, "file closed.")
            .await;
    }

    async fn semantic_tokens_full(
        &self,
        params: SemanticTokensParams,
    ) -> tower_lsp::jsonrpc::Result<Option<SemanticTokensResult>> {
        self.client
            .log_message(MessageType::INFO, "semantic tokens requested.")
            .await;
        let uri = params.text_document.uri;
        let cache = if let Some(r) = self.tokens.get(&uri) {
            if let TokenCache::Cached(t, _) = r.value() {
                Some(t.clone())
            } else {
                return Ok(None);
            }
        } else {
            None
        };
        if let Some(cache) = cache {
            Ok(Some(cache.into()))
        } else if let Ok(src) = fs::read_to_string(uri.path()) {
            self.client
                .log_message(MessageType::INFO, "compiling.")
                .await;
            if let Ok(Some(tokens)) = tokio::task::spawn_blocking(move || {
                semantic_tokens_from_src(&src)
            })
            .await
            {
                let semantic_tokens = tokens.0.clone();
                self.tokens
                    .insert(uri, TokenCache::Cached(tokens.0, tokens.1));
                Ok(Some(semantic_tokens.into()))
            } else {
                self.client
                    .log_message(
                        MessageType::INFO,
                        format!("could not compile {}.", uri),
                    )
                    .await;
                Ok(None)
            }
        } else {
            self.client
                .log_message(MessageType::INFO, format!("{} not found.", uri))
                .await;
            Ok(None)
        }
    }

    async fn hover(
        &self,
        params: HoverParams,
    ) -> tower_lsp::jsonrpc::Result<Option<Hover>> {
        let position = params.text_document_position_params.position;
        let url = params.text_document_position_params.text_document.uri;
        if let Some(hover_map) = self.tokens.get(&url) {
            if let TokenCache::Cached(_, h) = hover_map.value() {
                Ok(h.get(position.line as usize).and_then(|t| {
                    t.get(position.character as usize).cloned()?
                }))
            } else {
                Ok(None)
            }
        } else {
            Ok(None)
        }
    }
}

#[tokio::main]
pub async fn run() {
    let (stdin, stdout) = (tokio::io::stdin(), tokio::io::stdout());
    let (service, socket) = LspService::new(|client| Backend {
        client,
        tokens: Default::default(),
    });
    Server::new(stdin, stdout, socket).serve(service).await;
}

fn semantic_tokens_from_src(src: &str) -> Option<(SemanticTokens, HoverMap)> {
    let (char_to_utf16_map, utf16_to_char_map) = make_map(src);
    let (ts, src_len) = compiler::lex(src);
    let ast = compiler::parse_result(ts.clone(), src_len).ok()?;
    let TokenMapWithEnv {
        token_map,
        op_precedence_map,
    } = compiler::get_token_map(&ast).ok()?;
    let mut tokens = Vec::new();
    let mut line = 0;
    let mut start = 0;
    for (t, range) in &ts {
        use Token::*;
        let token_type = match t {
            Int(_) => SemanticTokenType::NUMBER,
            Str(_) => SemanticTokenType::STRING,
            Ident(s, id) => {
                if s == "()" {
                    continue;
                } else {
                    match token_map.get(id) {
                        Some(e) => match e {
                            TokenKind::GlobalVariable(_, Some(b))
                            | TokenKind::VariableDeclInInterface(b) => {
                                if b.t.is_function() {
                                    SemanticTokenType::FUNCTION
                                } else {
                                    SemanticTokenType::VARIABLE
                                }
                            }
                            TokenKind::LocalVariable(_, Some(t)) => {
                                if t.0.is_function() {
                                    SemanticTokenType::FUNCTION
                                } else {
                                    SemanticTokenType::VARIABLE
                                }
                            }
                            TokenKind::GlobalVariable(_, _)
                            | TokenKind::LocalVariable(_, _) => {
                                eprintln!("id = {id} ({s}) is variable but could not get its type.");
                                SemanticTokenType::VARIABLE
                            }
                            TokenKind::Type => SemanticTokenType::TYPE,
                            TokenKind::Constructor(_) => {
                                SemanticTokenType::new("constructor")
                            }
                            TokenKind::Interface => {
                                SemanticTokenType::INTERFACE
                            }
                        },
                        _ => {
                            eprintln!(
                                "id = {id} ({s}) is not found in token_map."
                            );
                            SemanticTokenType::VARIABLE
                        }
                    }
                }
            }
            Op(_, id) => {
                if let Some(TokenKind::Constructor(_)) = token_map.get(id) {
                    SemanticTokenType::new("constructorOperator")
                } else {
                    SemanticTokenType::OPERATOR
                }
            }
            Assign | Bar | BArrow | Colon | ColonColon | Question => {
                SemanticTokenType::OPERATOR
            }
            Paren(_) | OpenParenWithoutPad | Indent | Dedent | Comma => {
                continue
            }
            Case | Do | Forall | Infixl | Infixr | Data | Type | Interface
            | Mod | Where | Pub => SemanticTokenType::KEYWORD,
        };
        let l = char_to_utf16_map[range.start].0;
        let s = char_to_utf16_map[range.start].1;
        tokens.push(SemanticToken {
            delta_line: l - line,
            delta_start: if l == line { s - start } else { s },
            length: char_to_utf16_map[range.end].1 - s,
            token_type: SUPPORTED_TYPE_MAP[&token_type],
            token_modifiers_bitset: 0,
        });
        line = l;
        start = s;
    }
    let mut ts_tail = ts.iter();
    let mut ts_head = ts_tail.next().unwrap();
    let utf16_to_token_map = utf16_to_char_map
        .into_iter()
        .map(|utf16_to_char_line| {
            utf16_to_char_line
                .into_iter()
                .map(|char| {
                    char.and_then(|char| {
                        while ts_head.1.end <= char
                            || matches!(ts_head.0, Token::Dedent)
                        {
                            ts_head = ts_tail.next()?;
                        }
                        if ts_head.1.contains(&char) {
                            Some(Hover {
                                contents: HoverContents::Markup(
                                    MarkupContent {
                                        value: format!(
                                            "```\n{}\n```",
                                            print_type(
                                                &ts_head.0,
                                                &token_map,
                                                &op_precedence_map
                                            )?
                                        ),
                                        kind: MarkupKind::Markdown,
                                    },
                                ),
                                range: Some(Range {
                                    start: Position {
                                        line: char_to_utf16_map
                                            [ts_head.1.start]
                                            .0,
                                        character: char_to_utf16_map
                                            [ts_head.1.start]
                                            .1,
                                    },
                                    end: Position {
                                        line: char_to_utf16_map[ts_head.1.end]
                                            .0,
                                        character: char_to_utf16_map
                                            [ts_head.1.end]
                                            .1,
                                    },
                                }),
                            })
                        } else {
                            None
                        }
                    })
                })
                .collect()
        })
        .collect();
    Some((
        SemanticTokens {
            result_id: None,
            data: tokens,
        },
        utf16_to_token_map,
    ))
}

type Utf16ToCharMap = Vec<Vec<Option<usize>>>;

fn make_map(src: &str) -> (Vec<(u32, u32)>, Utf16ToCharMap) {
    let mut char_to_utf16_map = Vec::with_capacity(src.len());
    let mut utf16_to_char_map = Vec::new();
    let mut utf16_to_char_line = Vec::new();
    char_to_utf16_map.push((0, 0));
    let mut line = 0;
    let mut col_utf16 = 0;
    for (char_i, c) in src.chars().enumerate() {
        if c == '\n' {
            utf16_to_char_map.push(utf16_to_char_line);
            utf16_to_char_line = Vec::new();
            line += 1;
            col_utf16 = 0;
        } else {
            utf16_to_char_line.resize(col_utf16 as usize, None);
            col_utf16 += c.len_utf16() as u32;
        }
        utf16_to_char_line.push(Some(char_i));
        char_to_utf16_map.push((line, col_utf16));
    }
    utf16_to_char_map.push(utf16_to_char_line);
    (char_to_utf16_map, utf16_to_char_map)
}

fn print_type(
    token: &Token,
    token_map: &FxHashMap<TokenId, TokenKind>,
    op_precedence_map: &OpPrecedenceMap,
) -> Option<String> {
    match token {
        Token::Int(_) => Some("I64".to_string()),
        Token::Str(_) => Some("String".to_string()),
        Token::Ident(_, token_id) | Token::Op(_, token_id) => token_map
            .get(token_id)
            .and_then(|token_kind| match token_kind {
                TokenKind::GlobalVariable(_, Some(t))
                | TokenKind::VariableDeclInInterface(t)
                | TokenKind::Constructor(Some(t)) => Some(
                    PrintTypeOfGlobalVariableForUser {
                        t,
                        op_precedence_map,
                    }
                    .to_string(),
                ),
                TokenKind::LocalVariable(_, Some(t)) => Some(
                    PrintTypeOfLocalVariableForUser {
                        t: &t.0,
                        op_precedence_map,
                        type_variable_decls: &t.1,
                    }
                    .to_string(),
                ),
                _ => None,
            }),
        _ => None,
    }
}
