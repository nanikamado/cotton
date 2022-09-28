use compiler::{
    FxHashMap, OpPrecedenceMap, PrintForUser, PrintTypeOfLocalVariableForUser,
    Token, TokenId, TokenKind, TokenMapWithEnv, TypeMatchableRef,
};
use dashmap::DashMap;
use once_cell::sync::Lazy;
use std::collections::HashMap;
use std::fs;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

type HoverMap = Vec<Vec<Option<Hover>>>;

#[derive(Debug)]
struct Backend {
    client: Client,
    tokens: DashMap<Url, (SemanticTokens, HoverMap)>,
}

const SUPPORTED_TYPES: &[SemanticTokenType] = &[
    SemanticTokenType::STRING,
    SemanticTokenType::NUMBER,
    SemanticTokenType::TYPE,
    SemanticTokenType::STRUCT,
    SemanticTokenType::INTERFACE,
    SemanticTokenType::FUNCTION,
    SemanticTokenType::VARIABLE,
    SemanticTokenType::KEYWORD,
    SemanticTokenType::COMMENT,
    SemanticTokenType::OPERATOR,
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
        let src = params.text_document.text;
        let tokens =
            tokio::task::spawn_blocking(move || semantic_tokens_from_src(&src))
                .await
                .unwrap();
        self.tokens.insert(params.text_document.uri, tokens);
    }

    async fn did_change(&self, _params: DidChangeTextDocumentParams) {
        self.client
            .log_message(MessageType::INFO, "file changed")
            .await;
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        let path = params.text_document.uri.path();
        if let Ok(src) = fs::read_to_string(path) {
            let tokens = tokio::task::spawn_blocking(move || {
                semantic_tokens_from_src(&src)
            })
            .await
            .unwrap();
            self.tokens.insert(params.text_document.uri, tokens);
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
        let uri = params.text_document.uri;
        if let Some(r) = self.tokens.get(&uri) {
            let tokens = r.value();
            Ok(Some(tokens.0.clone().into()))
        } else if let Ok(src) = fs::read_to_string(uri.path()) {
            let tokens = tokio::task::spawn_blocking(move || {
                semantic_tokens_from_src(&src)
            })
            .await
            .unwrap();
            let semantic_tokens = tokens.0.clone();
            self.tokens.insert(uri, tokens);
            Ok(Some(semantic_tokens.into()))
        } else {
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
            Ok(hover_map
                .value()
                .1
                .get(position.line as usize)
                .and_then(|t| t.get(position.character as usize).cloned()?))
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

fn semantic_tokens_from_src(src: &str) -> (SemanticTokens, HoverMap) {
    let (char_to_utf16_map, utf16_to_char_map) = make_map(src);
    let (ts, src_len) = compiler::lex(src);
    let ast = compiler::parse(ts.clone(), src, src_len);
    let TokenMapWithEnv {
        token_map,
        op_precedence_map,
    } = compiler::get_token_map(&ast);
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
                                if let TypeMatchableRef::Fn(_, _) =
                                    b.constructor.matchable_ref()
                                {
                                    SemanticTokenType::FUNCTION
                                } else {
                                    SemanticTokenType::VARIABLE
                                }
                            }
                            TokenKind::LocalVariable(_, Some(t)) => {
                                if let TypeMatchableRef::Fn(_, _) =
                                    t.matchable_ref()
                                {
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
                                SemanticTokenType::STRUCT
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
            Op(_, _) | Assign | Bar | BArrow | Colon => {
                SemanticTokenType::OPERATOR
            }
            Paren(_) | OpenParenWithoutPad | Indent | Dedent | Comma => {
                continue
            }
            Case | Do | Forall | Infixl | Infixr | Data | Type | Interface
            | Where => SemanticTokenType::KEYWORD,
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
    (
        SemanticTokens {
            result_id: None,
            data: tokens,
        },
        utf16_to_token_map,
    )
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
                | TokenKind::Constructor(Some(t)) => {
                    Some(PrintForUser(t, op_precedence_map).to_string())
                }
                TokenKind::LocalVariable(_, Some(t)) => Some(
                    PrintTypeOfLocalVariableForUser {
                        t,
                        op_precedence_map,
                    }
                    .to_string(),
                ),
                _ => None,
            }),
        _ => None,
    }
}
