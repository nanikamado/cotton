use cotton::{Token, TokenKind, TypeMatchableRef};
use dashmap::DashMap;
use once_cell::sync::Lazy;
use std::collections::HashMap;
use std::fs;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

#[derive(Debug)]
struct Backend {
    client: Client,
    tokens: DashMap<Url, SemanticTokens>,
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
            .log_message(MessageType::INFO, "Initializing ...")
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
                ..ServerCapabilities::default()
            },
            ..Default::default()
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        self.client
            .log_message(MessageType::INFO, "initialized!")
            .await;
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    async fn did_change_configuration(&self, _: DidChangeConfigurationParams) {
        self.client
            .log_message(MessageType::INFO, "configuration changed!")
            .await;
    }

    async fn did_change_watched_files(&self, _: DidChangeWatchedFilesParams) {
        self.client
            .log_message(MessageType::INFO, "watched files have changed!")
            .await;
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        self.client
            .log_message(MessageType::INFO, "file opened!")
            .await;
        let src = params.text_document.text;
        let tokens =
            tokio::task::spawn_blocking(move || semantic_tokens_from_src(&src))
                .await
                .unwrap();
        self.tokens.insert(params.text_document.uri, tokens);
    }

    async fn did_change(&self, _params: DidChangeTextDocumentParams) {
        self.client
            .log_message(MessageType::INFO, "file changed!")
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
            self.client
                .log_message(
                    MessageType::INFO,
                    format!("file saved. tokens saved."),
                )
                .await;
        }
    }

    async fn did_close(&self, _: DidCloseTextDocumentParams) {
        self.client
            .log_message(MessageType::INFO, "file closed!")
            .await;
    }

    async fn semantic_tokens_full(
        &self,
        params: SemanticTokensParams,
    ) -> tower_lsp::jsonrpc::Result<Option<SemanticTokensResult>> {
        let uri = params.text_document.uri;
        if let Some(r) = self.tokens.get(&uri) {
            let tokens = r.value();
            Ok(Some(tokens.clone().into()))
        } else {
            if let Ok(src) = fs::read_to_string(uri.path()) {
                let tokens = tokio::task::spawn_blocking(move || {
                    semantic_tokens_from_src(&src)
                })
                .await
                .unwrap();
                self.tokens.insert(uri, tokens.clone());
                Ok(Some(tokens.into()))
            } else {
                Ok(None)
            }
        }
    }
}

#[tokio::main]
async fn main() {
    let (stdin, stdout) = (tokio::io::stdin(), tokio::io::stdout());
    let (service, socket) = LspService::new(|client| Backend {
        client,
        tokens: Default::default(),
    });
    Server::new(stdin, stdout, socket).serve(service).await;
}

fn semantic_tokens_from_src(src: &str) -> SemanticTokens {
    let char_to_utf16_map = make_map(&src);
    let (ts, src_len) = cotton::lex(&src);
    let ast = cotton::parse(ts.clone(), src, src_len);
    let token_map = cotton::get_token_map(&ast);
    let mut tokens = Vec::new();
    let mut line = 0;
    let mut start = 0;
    for (t, range) in ts {
        use Token::*;
        let token_type = match t {
            Int(_) => SemanticTokenType::NUMBER,
            Str(_) => SemanticTokenType::STRING,
            Ident(s, id) => {
                if s == "()" {
                    continue;
                } else {
                    match token_map.get(&id) {
                        Some(e) => match e {
                            TokenKind::Variable(_, Some(b))
                            | TokenKind::VariableDeclInInterface(b) => {
                                if let TypeMatchableRef::Fn(_, _) =
                                    b.constructor.matchable_ref()
                                {
                                    SemanticTokenType::FUNCTION
                                } else {
                                    SemanticTokenType::VARIABLE
                                }
                            }
                            TokenKind::Variable(_, _) => {
                                eprintln!("id = {id} ({s}) is variable but could not get its type.");
                                SemanticTokenType::VARIABLE
                            }
                            TokenKind::Type => SemanticTokenType::TYPE,
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
    SemanticTokens {
        result_id: None,
        data: tokens,
    }
}

fn make_map(src: &str) -> Vec<(u32, u32)> {
    let src = src.chars();
    let mut char_to_utf16_map = Vec::with_capacity(src.size_hint().0);
    char_to_utf16_map.push((0, 0));
    let mut line = 0;
    let mut col = 0;
    for c in src {
        if c == '\n' {
            line += 1;
            col = 0;
        } else {
            col += c.len_utf16() as u32;
        }
        char_to_utf16_map.push((line, col));
    }
    char_to_utf16_map
}
