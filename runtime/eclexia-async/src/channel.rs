// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Channel primitives for Eclexia concurrency.
//!
//! Provides MPSC (multi-producer, single-consumer), oneshot, and broadcast
//! channels built on tokio's channel implementations.
//!
//! All channels integrate with Eclexia's resource tracking system.

use std::fmt;

/// Error type for channel operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ChannelError {
    /// The channel is closed (all senders or the receiver dropped).
    Closed,
    /// The channel is full (for bounded channels).
    Full,
    /// A lagged broadcast receiver missed messages.
    Lagged(u64),
}

impl fmt::Display for ChannelError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Closed => write!(f, "channel closed"),
            Self::Full => write!(f, "channel full"),
            Self::Lagged(n) => write!(f, "receiver lagged by {} messages", n),
        }
    }
}

impl std::error::Error for ChannelError {}

/// A generic channel type that can be MPSC, oneshot, or broadcast.
#[derive(Debug)]
pub enum Channel<T> {
    /// Multi-producer, single-consumer bounded channel.
    Mpsc {
        sender: tokio::sync::mpsc::Sender<T>,
        receiver: Option<tokio::sync::mpsc::Receiver<T>>,
    },
}

/// Sender half of an MPSC channel.
#[derive(Debug, Clone)]
pub struct Sender<T> {
    inner: tokio::sync::mpsc::Sender<T>,
}

impl<T: Send> Sender<T> {
    /// Send a value on the channel, waiting if necessary.
    pub async fn send(&self, value: T) -> Result<(), ChannelError> {
        self.inner
            .send(value)
            .await
            .map_err(|_| ChannelError::Closed)
    }

    /// Try to send a value without waiting.
    pub fn try_send(&self, value: T) -> Result<(), ChannelError> {
        self.inner.try_send(value).map_err(|e| match e {
            tokio::sync::mpsc::error::TrySendError::Full(_) => ChannelError::Full,
            tokio::sync::mpsc::error::TrySendError::Closed(_) => ChannelError::Closed,
        })
    }

    /// Check if the channel is closed.
    pub fn is_closed(&self) -> bool {
        self.inner.is_closed()
    }
}

/// Receiver half of an MPSC channel.
#[derive(Debug)]
pub struct Receiver<T> {
    inner: tokio::sync::mpsc::Receiver<T>,
}

impl<T: Send> Receiver<T> {
    /// Receive a value from the channel, waiting if necessary.
    pub async fn recv(&mut self) -> Result<T, ChannelError> {
        self.inner.recv().await.ok_or(ChannelError::Closed)
    }

    /// Try to receive a value without waiting.
    pub fn try_recv(&mut self) -> Result<T, ChannelError> {
        self.inner.try_recv().map_err(|e| match e {
            tokio::sync::mpsc::error::TryRecvError::Empty => ChannelError::Full,
            tokio::sync::mpsc::error::TryRecvError::Disconnected => ChannelError::Closed,
        })
    }
}

/// Create a bounded MPSC (multi-producer, single-consumer) channel.
///
/// The channel can buffer up to `capacity` messages before senders block.
pub fn mpsc<T: Send>(capacity: usize) -> (Sender<T>, Receiver<T>) {
    let (tx, rx) = tokio::sync::mpsc::channel(capacity);
    (Sender { inner: tx }, Receiver { inner: rx })
}

/// Sender half of a oneshot channel.
#[derive(Debug)]
pub struct OneshotSender<T> {
    inner: tokio::sync::oneshot::Sender<T>,
}

impl<T: Send> OneshotSender<T> {
    /// Send a single value. Consumes the sender.
    pub fn send(self, value: T) -> Result<(), ChannelError> {
        self.inner.send(value).map_err(|_| ChannelError::Closed)
    }
}

/// Receiver half of a oneshot channel.
#[derive(Debug)]
pub struct OneshotReceiver<T> {
    inner: tokio::sync::oneshot::Receiver<T>,
}

impl<T: Send> std::future::Future for OneshotReceiver<T> {
    type Output = Result<T, ChannelError>;

    fn poll(
        mut self: std::pin::Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Self::Output> {
        use std::pin::Pin;
        use std::task::Poll;

        match Pin::new(&mut self.inner).poll(cx) {
            Poll::Ready(Ok(val)) => Poll::Ready(Ok(val)),
            Poll::Ready(Err(_)) => Poll::Ready(Err(ChannelError::Closed)),
            Poll::Pending => Poll::Pending,
        }
    }
}

/// Create a oneshot channel for sending a single value.
pub fn oneshot<T: Send>() -> (OneshotSender<T>, OneshotReceiver<T>) {
    let (tx, rx) = tokio::sync::oneshot::channel();
    (OneshotSender { inner: tx }, OneshotReceiver { inner: rx })
}

/// Sender half of a broadcast channel. Cloneable — all clones send to
/// the same set of receivers.
#[derive(Debug, Clone)]
pub struct BroadcastSender<T: Clone> {
    inner: tokio::sync::broadcast::Sender<T>,
}

impl<T: Clone + Send> BroadcastSender<T> {
    /// Send a value to all receivers.
    pub fn send(&self, value: T) -> Result<(), ChannelError> {
        self.inner
            .send(value)
            .map(|_| ())
            .map_err(|_| ChannelError::Closed)
    }

    /// Subscribe a new receiver to this broadcast channel.
    pub fn subscribe(&self) -> BroadcastReceiver<T> {
        BroadcastReceiver {
            inner: self.inner.subscribe(),
        }
    }
}

/// Receiver half of a broadcast channel.
#[derive(Debug)]
pub struct BroadcastReceiver<T: Clone> {
    inner: tokio::sync::broadcast::Receiver<T>,
}

impl<T: Clone + Send> BroadcastReceiver<T> {
    /// Receive the next value from the broadcast channel.
    pub async fn recv(&mut self) -> Result<T, ChannelError> {
        self.inner.recv().await.map_err(|e| match e {
            tokio::sync::broadcast::error::RecvError::Closed => ChannelError::Closed,
            tokio::sync::broadcast::error::RecvError::Lagged(n) => ChannelError::Lagged(n),
        })
    }
}

/// Create a broadcast channel with the given capacity.
///
/// All receivers see every message. If a receiver falls behind by more
/// than `capacity` messages, it receives a `Lagged` error.
pub fn broadcast<T: Clone + Send>(capacity: usize) -> (BroadcastSender<T>, BroadcastReceiver<T>) {
    let (tx, rx) = tokio::sync::broadcast::channel(capacity);
    (
        BroadcastSender { inner: tx },
        BroadcastReceiver { inner: rx },
    )
}
