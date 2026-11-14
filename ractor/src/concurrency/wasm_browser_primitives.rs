// Copyright (c) Sean Lawlor
//
// This source code is licensed under both the MIT license found in the
// LICENSE-MIT file in the root directory of this source tree.

//! Tokio tasks driven by the browser's JavaScript executor.
//! This implementation only works in a browser environment and is not suitable for server-side wasm use.

mod time;

use std::future::Future;
use std::rc::Rc;

thread_local! {
    // Keep the set driven even when temporarily empty, so later spawns wake it.
    static TASKS: Rc<tokio::task::LocalSet> = {
        let tasks = Rc::new(tokio::task::LocalSet::new());
        let driver = tasks.clone();
        wasm_bindgen_futures::spawn_local(async move {
            driver.run_until(std::future::pending::<()>()).await;
        });
        tasks
    };
}

/// Represents a task JoinHandle
pub type JoinHandle<T> = tokio::task::JoinHandle<T>;

/// A duration of time
pub type Duration = std::time::Duration;

/// An instant measured on system time
pub type Instant = web_time::Instant;

/// Sleep the task for a duration of time
pub fn sleep(dur: Duration) -> impl Future<Output = ()> + Send {
    time::sleep(dur)
}

/// An asynchronous interval calculation which waits until
/// a checkpoint time to tick
pub type Interval = time::Interval;

/// Build a new interval at the given duration starting at now
///
/// Ticks 1 time immediately
pub fn interval(dur: Duration) -> Interval {
    time::interval(dur)
}

/// A set of futures to join on, in an unordered fashion
/// (first-completed, first-served)
#[derive(Debug)]
pub struct JoinSet<T> {
    inner: tokio::task::JoinSet<T>,
}

impl<T: 'static> Default for JoinSet<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: 'static> JoinSet<T> {
    /// Create an empty set of browser tasks.
    pub fn new() -> Self {
        Self {
            inner: tokio::task::JoinSet::new(),
        }
    }

    /// Spawn on the browser executor, without requiring a Tokio runtime.
    pub fn spawn<F: Future<Output = T> + 'static>(
        &mut self,
        future: F,
    ) -> tokio::task::AbortHandle {
        TASKS.with(|tasks| self.inner.spawn_local_on(future, tasks))
    }

    /// Wait for the next task to complete. Cancel safe, as on native Tokio.
    pub async fn join_next(&mut self) -> Option<Result<T, tokio::task::JoinError>> {
        self.inner.join_next().await
    }

    /// Return a completed task without waiting.
    pub fn try_join_next(&mut self) -> Option<Result<T, tokio::task::JoinError>> {
        self.inner.try_join_next()
    }

    /// Poll for the next completed task.
    pub fn poll_join_next(
        &mut self,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Option<Result<T, tokio::task::JoinError>>> {
        self.inner.poll_join_next(cx)
    }

    /// Collect all outputs, panicking if a task failed, as on native Tokio.
    pub async fn join_all(self) -> Vec<T> {
        self.inner.join_all().await
    }

    /// Number of tasks still in the set.
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Whether the set is empty.
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Abort all tasks without removing them from the set.
    pub fn abort_all(&mut self) {
        self.inner.abort_all();
    }

    /// Detach all tasks, allowing them to continue running.
    pub fn detach_all(&mut self) {
        self.inner.detach_all();
    }

    /// Abort and wait for all tasks to finish.
    pub async fn shutdown(&mut self) {
        self.inner.shutdown().await;
    }
}

/// Spawn a task on the executor runtime
pub fn spawn<F>(future: F) -> JoinHandle<F::Output>
where
    F: Future + Send + 'static,
    F::Output: Send + 'static,
{
    spawn_named(None, future)
}

/// Spawn a task on the executor runtime which will not be moved to other threads
pub fn spawn_local<F>(future: F) -> JoinHandle<F::Output>
where
    F: Future + 'static,
{
    TASKS.with(|tasks| tasks.spawn_local(future))
}

/// Spawn a (possibly) named task on the executor runtime
pub fn spawn_named<F>(name: Option<&str>, future: F) -> JoinHandle<F::Output>
where
    F: Future + Send + 'static,
    F::Output: Send + 'static,
{
    let _ = name;
    spawn_local(future)
}

/// Execute the future up to a timeout
///
/// * `dur`: The duration of time to allow the future to execute for
/// * `future`: The future to execute
///
/// Returns [Ok(_)] if the future succeeded before the timeout, [Err(super::Timeout)] otherwise
pub async fn timeout<F, T>(dur: super::Duration, future: F) -> Result<T, super::Timeout>
where
    F: Future<Output = T>,
{
    time::timeout(dur, future).await.map_err(|_| super::Timeout)
}

macro_rules! select {
        ($($tokens:tt)*) => {{
            tokio::select! {
                // Biased ensures that we poll the ports in the order they appear, giving
                // priority to our message reception operations. See:
                // https://docs.rs/tokio/latest/tokio/macro.select.html#fairness
                // for more information
                biased;

                $( $tokens )*
            }
        }}
    }

pub(crate) use select;
// test macro
#[cfg(test)]
pub use wasm_bindgen_test::wasm_bindgen_test as test;
