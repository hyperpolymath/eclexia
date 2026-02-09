// SPDX-License-Identifier: PMPL-1.0-or-later
//! eclexia-tea: The Elm Architecture (TEA) runtime for Eclexia
//!
//! Provides a Model-Update-View loop for building interactive applications
//! with Eclexia, targeting both native and WASM execution.

use serde::{Deserialize, Serialize};
use std::fmt;

/// A command represents a side effect to be performed
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Cmd<Msg> {
    /// No effect
    None,
    /// Batch multiple commands
    Batch(Vec<Cmd<Msg>>),
    /// HTTP request that produces a message on completion
    Http {
        method: String,
        url: String,
        body: Option<String>,
        #[serde(skip)]
        on_response: Option<Box<dyn Fn(Result<String, String>) -> Msg + Send + Sync>>,
    },
    /// Timer that fires after delay_ms milliseconds
    Timer {
        delay_ms: u64,
        #[serde(skip)]
        on_tick: Option<Box<dyn Fn() -> Msg + Send + Sync>>,
    },
    /// Custom command with serialized payload
    Custom {
        kind: String,
        payload: serde_json::Value,
    },
}

impl<Msg> Default for Cmd<Msg> {
    fn default() -> Self {
        Cmd::None
    }
}

/// A subscription represents an ongoing event source
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Sub<Msg> {
    /// No subscription
    None,
    /// Batch multiple subscriptions
    Batch(Vec<Sub<Msg>>),
    /// Timer subscription that fires every interval_ms
    OnTimer {
        interval_ms: u64,
        #[serde(skip)]
        to_msg: Option<Box<dyn Fn(f64) -> Msg + Send + Sync>>,
    },
    /// DOM event subscription
    OnEvent {
        event_name: String,
        selector: String,
        #[serde(skip)]
        to_msg: Option<Box<dyn Fn(String) -> Msg + Send + Sync>>,
    },
}

impl<Msg> Default for Sub<Msg> {
    fn default() -> Self {
        Sub::None
    }
}

/// Virtual DOM node representation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Html {
    /// Element node
    Element {
        tag: String,
        attrs: Vec<(String, String)>,
        children: Vec<Html>,
    },
    /// Text node
    Text(String),
    /// Empty node
    Empty,
}

impl Html {
    /// Create an element node
    pub fn element(tag: &str, attrs: Vec<(&str, &str)>, children: Vec<Html>) -> Self {
        Html::Element {
            tag: tag.to_string(),
            attrs: attrs.into_iter().map(|(k, v)| (k.to_string(), v.to_string())).collect(),
            children,
        }
    }

    /// Create a text node
    pub fn text(content: &str) -> Self {
        Html::Text(content.to_string())
    }

    /// Convenience: create a div
    pub fn div(attrs: Vec<(&str, &str)>, children: Vec<Html>) -> Self {
        Self::element("div", attrs, children)
    }

    /// Convenience: create a paragraph
    pub fn p(attrs: Vec<(&str, &str)>, children: Vec<Html>) -> Self {
        Self::element("p", attrs, children)
    }

    /// Convenience: create a heading
    pub fn h1(attrs: Vec<(&str, &str)>, children: Vec<Html>) -> Self {
        Self::element("h1", attrs, children)
    }

    /// Convenience: create a button
    pub fn button(attrs: Vec<(&str, &str)>, children: Vec<Html>) -> Self {
        Self::element("button", attrs, children)
    }

    /// Convenience: create an input
    pub fn input(attrs: Vec<(&str, &str)>) -> Self {
        Self::element("input", attrs, vec![])
    }

    /// Render to HTML string
    pub fn render(&self) -> String {
        match self {
            Html::Element { tag, attrs, children } => {
                let attr_str = if attrs.is_empty() {
                    String::new()
                } else {
                    let parts: Vec<String> = attrs
                        .iter()
                        .map(|(k, v)| format!("{}=\"{}\"", k, v))
                        .collect();
                    format!(" {}", parts.join(" "))
                };

                let children_str: String = children.iter().map(|c| c.render()).collect();

                // Self-closing tags
                if children.is_empty() && matches!(tag.as_str(), "input" | "br" | "hr" | "img" | "meta" | "link") {
                    format!("<{}{} />", tag, attr_str)
                } else {
                    format!("<{}{}>{}</{}>", tag, attr_str, children_str, tag)
                }
            }
            Html::Text(content) => content.clone(),
            Html::Empty => String::new(),
        }
    }
}

impl fmt::Display for Html {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.render())
    }
}

/// The TEA application trait
///
/// Implement this to define your application's behaviour.
pub trait App: Sized + 'static {
    /// The model type (application state)
    type Model: Clone + fmt::Debug;
    /// The message type (events/actions)
    type Msg: Clone + fmt::Debug;

    /// Initialize the model and optional startup command
    fn init(&self) -> (Self::Model, Cmd<Self::Msg>);

    /// Update the model in response to a message
    fn update(&self, model: &Self::Model, msg: Self::Msg) -> (Self::Model, Cmd<Self::Msg>);

    /// Render the model as a virtual DOM tree
    fn view(&self, model: &Self::Model) -> Html;

    /// Define active subscriptions based on current model
    fn subscriptions(&self, _model: &Self::Model) -> Sub<Self::Msg> {
        Sub::None
    }
}

/// TEA program runner
///
/// Manages the Model-Update-View loop for an `App`.
pub struct Program<A: App> {
    app: A,
    model: A::Model,
    rendered: String,
}

impl<A: App> Program<A> {
    /// Create a new program from an App
    pub fn new(app: A) -> Self {
        let (model, _cmd) = app.init();
        let rendered = app.view(&model).render();
        Program { app, model, rendered }
    }

    /// Get the current model
    pub fn model(&self) -> &A::Model {
        &self.model
    }

    /// Get the last rendered HTML
    pub fn rendered_html(&self) -> &str {
        &self.rendered
    }

    /// Dispatch a message to the program
    pub fn dispatch(&mut self, msg: A::Msg) -> Cmd<A::Msg> {
        let (new_model, cmd) = self.app.update(&self.model, msg);
        self.model = new_model;
        self.rendered = self.app.view(&self.model).render();
        cmd
    }

    /// Get the current view
    pub fn view(&self) -> Html {
        self.app.view(&self.model)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Debug)]
    struct CounterModel {
        count: i32,
    }

    #[derive(Clone, Debug)]
    enum CounterMsg {
        Increment,
        Decrement,
        Reset,
    }

    struct CounterApp;

    impl App for CounterApp {
        type Model = CounterModel;
        type Msg = CounterMsg;

        fn init(&self) -> (CounterModel, Cmd<CounterMsg>) {
            (CounterModel { count: 0 }, Cmd::None)
        }

        fn update(&self, model: &CounterModel, msg: CounterMsg) -> (CounterModel, Cmd<CounterMsg>) {
            let new_model = match msg {
                CounterMsg::Increment => CounterModel { count: model.count + 1 },
                CounterMsg::Decrement => CounterModel { count: model.count - 1 },
                CounterMsg::Reset => CounterModel { count: 0 },
            };
            (new_model, Cmd::None)
        }

        fn view(&self, model: &CounterModel) -> Html {
            Html::div(vec![], vec![
                Html::h1(vec![], vec![Html::text(&format!("Count: {}", model.count))]),
                Html::button(vec![("id", "inc")], vec![Html::text("+")]),
                Html::button(vec![("id", "dec")], vec![Html::text("-")]),
                Html::button(vec![("id", "reset")], vec![Html::text("Reset")]),
            ])
        }
    }

    #[test]
    fn test_program_init() {
        let program = Program::new(CounterApp);
        assert_eq!(program.model().count, 0);
    }

    #[test]
    fn test_program_dispatch() {
        let mut program = Program::new(CounterApp);
        program.dispatch(CounterMsg::Increment);
        assert_eq!(program.model().count, 1);
        program.dispatch(CounterMsg::Increment);
        assert_eq!(program.model().count, 2);
        program.dispatch(CounterMsg::Decrement);
        assert_eq!(program.model().count, 1);
    }

    #[test]
    fn test_program_reset() {
        let mut program = Program::new(CounterApp);
        program.dispatch(CounterMsg::Increment);
        program.dispatch(CounterMsg::Increment);
        program.dispatch(CounterMsg::Reset);
        assert_eq!(program.model().count, 0);
    }

    #[test]
    fn test_html_render() {
        let html = Html::div(
            vec![("class", "container")],
            vec![
                Html::h1(vec![], vec![Html::text("Hello")]),
                Html::p(vec![], vec![Html::text("World")]),
            ],
        );
        let rendered = html.render();
        assert!(rendered.contains("<div class=\"container\">"));
        assert!(rendered.contains("<h1>Hello</h1>"));
        assert!(rendered.contains("<p>World</p>"));
        assert!(rendered.contains("</div>"));
    }

    #[test]
    fn test_html_self_closing() {
        let html = Html::input(vec![("type", "text"), ("placeholder", "Enter...")]);
        let rendered = html.render();
        assert!(rendered.contains("<input"));
        assert!(rendered.contains("/>"));
    }
}
