// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! The Elm Architecture (TEA) for Eclexia.
//!
//! Provides a Model-Update-View loop for building interactive applications
//! with Eclexia, targeting both native and WASM execution.
//!
//! Backed by the eclexia-tea runtime crate.

// === Core Types ===

/// Command type for side effects produced by update functions.
///
/// Commands describe effects to be performed by the runtime,
/// without executing them directly. This keeps the update function pure.
type Cmd<Msg> {
    /// No side effect.
    CmdNone,
    /// Batch multiple commands together.
    CmdBatch(List<Cmd<Msg>>),
    /// Perform an HTTP request.
    CmdHttp {
        method: String,
        url: String,
        body: Option<String>,
        on_response: (Result<String, String>) -> Msg,
    },
    /// Set a timer that fires after delay_ms milliseconds.
    CmdTimer {
        delay_ms: Int,
        on_tick: () -> Msg,
    },
    /// Custom command with a string payload.
    CmdCustom {
        kind: String,
        payload: String,
    },
}

/// Subscription type for ongoing event sources.
///
/// Subscriptions describe continuous event streams that the runtime
/// manages. They are recalculated after each model update.
type Sub<Msg> {
    /// No subscription.
    SubNone,
    /// Batch multiple subscriptions.
    SubBatch(List<Sub<Msg>>),
    /// Timer that fires every interval_ms milliseconds.
    SubOnTimer {
        interval_ms: Int,
        to_msg: (Float) -> Msg,
    },
    /// DOM event subscription.
    SubOnEvent {
        event_name: String,
        selector: String,
        to_msg: (String) -> Msg,
    },
}

/// Virtual DOM node for describing UI structure.
///
/// Represents a tree of HTML-like elements that can be rendered
/// to a string or diffed for efficient DOM updates.
type Html {
    /// An element node with tag, attributes, and children.
    Element {
        tag: String,
        attrs: List<(String, String)>,
        children: List<Html>,
    },
    /// A text node.
    Text(String),
    /// An empty node (renders nothing).
    Empty,
}

// === App Trait ===

/// The TEA application trait.
///
/// Implement this to define your application's behaviour.
/// The runtime manages the Model-Update-View loop.
///
/// # Example
/// ```
/// type CounterModel { count: Int }
/// type CounterMsg { Increment, Decrement, Reset }
///
/// impl App for CounterApp {
///     type Model = CounterModel
///     type Msg = CounterMsg
///
///     fn init() -> (CounterModel, Cmd<CounterMsg>) {
///         (CounterModel { count: 0 }, CmdNone)
///     }
///
///     fn update(model: CounterModel, msg: CounterMsg) -> (CounterModel, Cmd<CounterMsg>) {
///         match msg {
///             Increment => (CounterModel { count: model.count + 1 }, CmdNone),
///             Decrement => (CounterModel { count: model.count - 1 }, CmdNone),
///             Reset => (CounterModel { count: 0 }, CmdNone),
///         }
///     }
///
///     fn view(model: CounterModel) -> Html {
///         div([], [
///             h1([], [text(to_string(model.count))]),
///             button([("id", "inc")], [text("+")]),
///             button([("id", "dec")], [text("-")]),
///         ])
///     }
/// }
/// ```
trait App {
    type Model;
    type Msg;

    /// Initialize the model and optional startup command.
    fn init() -> (Self.Model, Cmd<Self.Msg>);

    /// Update the model in response to a message.
    fn update(model: Self.Model, msg: Self.Msg) -> (Self.Model, Cmd<Self.Msg>);

    /// Render the model as a virtual DOM tree.
    fn view(model: Self.Model) -> Html;

    /// Define active subscriptions based on current model.
    /// Default implementation returns no subscriptions.
    fn subscriptions(model: Self.Model) -> Sub<Self.Msg> {
        SubNone
    }
}

// === Html Constructors ===

/// Create an element node.
fn element(tag: String, attrs: List<(String, String)>, children: List<Html>) -> Html {
    Element { tag: tag, attrs: attrs, children: children }
}

/// Create a text node.
fn text(content: String) -> Html {
    Text(content)
}

/// Create a div element.
fn div(attrs: List<(String, String)>, children: List<Html>) -> Html {
    element("div", attrs, children)
}

/// Create a paragraph element.
fn p(attrs: List<(String, String)>, children: List<Html>) -> Html {
    element("p", attrs, children)
}

/// Create a heading (h1) element.
fn h1(attrs: List<(String, String)>, children: List<Html>) -> Html {
    element("h1", attrs, children)
}

/// Create a heading (h2) element.
fn h2(attrs: List<(String, String)>, children: List<Html>) -> Html {
    element("h2", attrs, children)
}

/// Create a heading (h3) element.
fn h3(attrs: List<(String, String)>, children: List<Html>) -> Html {
    element("h3", attrs, children)
}

/// Create a span element.
fn span(attrs: List<(String, String)>, children: List<Html>) -> Html {
    element("span", attrs, children)
}

/// Create a button element.
fn button(attrs: List<(String, String)>, children: List<Html>) -> Html {
    element("button", attrs, children)
}

/// Create an input element (self-closing).
fn input(attrs: List<(String, String)>) -> Html {
    element("input", attrs, [])
}

/// Create an anchor (link) element.
fn a(attrs: List<(String, String)>, children: List<Html>) -> Html {
    element("a", attrs, children)
}

/// Create an unordered list element.
fn ul(attrs: List<(String, String)>, children: List<Html>) -> Html {
    element("ul", attrs, children)
}

/// Create a list item element.
fn li(attrs: List<(String, String)>, children: List<Html>) -> Html {
    element("li", attrs, children)
}

/// Create a form element.
fn form(attrs: List<(String, String)>, children: List<Html>) -> Html {
    element("form", attrs, children)
}

/// Create a section element.
fn section(attrs: List<(String, String)>, children: List<Html>) -> Html {
    element("section", attrs, children)
}

/// Create a nav element.
fn nav(attrs: List<(String, String)>, children: List<Html>) -> Html {
    element("nav", attrs, children)
}

// === Html Rendering ===

/// Render an Html node to an HTML string.
@builtin("tea_render")
fn render(html: Html) -> String;

// === Program Runner ===

/// Start a TEA program with the given App implementation.
///
/// This initialises the model, renders the initial view, and
/// enters the Model-Update-View loop.
@builtin("tea_program_run")
fn run<A: App>(app: A) -> ();

/// Mount a TEA program onto a DOM selector (WASM target).
///
/// Like `run`, but mounts the rendered output into the specified
/// DOM element in the browser.
@builtin("tea_program_mount")
fn mount<A: App>(app: A, selector: String) -> ();

// === Cmd Helpers ===

/// Create an HTTP GET command.
fn http_get(url: String, on_response: (Result<String, String>) -> Msg) -> Cmd<Msg> {
    CmdHttp { method: "GET", url: url, body: None, on_response: on_response }
}

/// Create an HTTP POST command.
fn http_post(url: String, body: String, on_response: (Result<String, String>) -> Msg) -> Cmd<Msg> {
    CmdHttp { method: "POST", url: url, body: Some(body), on_response: on_response }
}

/// Batch a list of commands into a single command.
fn batch_cmds(cmds: List<Cmd<Msg>>) -> Cmd<Msg> {
    CmdBatch(cmds)
}

/// Create a timer command that fires once after delay_ms milliseconds.
fn after(delay_ms: Int, msg: Msg) -> Cmd<Msg> {
    CmdTimer { delay_ms: delay_ms, on_tick: || msg }
}

// === Sub Helpers ===

/// Subscribe to a repeating timer.
fn every(interval_ms: Int, to_msg: (Float) -> Msg) -> Sub<Msg> {
    SubOnTimer { interval_ms: interval_ms, to_msg: to_msg }
}

/// Subscribe to a DOM event on elements matching a selector.
fn on_event(event_name: String, selector: String, to_msg: (String) -> Msg) -> Sub<Msg> {
    SubOnEvent { event_name: event_name, selector: selector, to_msg: to_msg }
}

/// Batch a list of subscriptions.
fn batch_subs(subs: List<Sub<Msg>>) -> Sub<Msg> {
    SubBatch(subs)
}
