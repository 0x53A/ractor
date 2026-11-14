// Copyright (c) Sean Lawlor
//
// This source code is licensed under both the MIT license found in the
// LICENSE-MIT file in the root directory of this source tree.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use super::*;

#[super::test]
async fn timeout_accepts_borrowed_non_send_futures() {
    let value = std::rc::Rc::new(String::from("borrowed"));
    let result = timeout(Duration::from_secs(2), async {
        sleep(Duration::from_millis(1)).await;
        value.as_str()
    })
    .await
    .unwrap();
    assert_eq!(result, "borrowed");
}

struct Dropped(Arc<AtomicBool>);

impl Drop for Dropped {
    fn drop(&mut self) {
        self.0.store(true, Ordering::SeqCst);
    }
}

#[super::test]
async fn abort_drops_the_task() {
    let dropped = Arc::new(AtomicBool::new(false));
    let guard = Dropped(dropped.clone());
    let (started, ready) = oneshot();
    let handle = spawn(async move {
        let _guard = guard;
        started.send(()).unwrap();
        std::future::pending::<()>().await;
    });
    ready.await.unwrap();
    handle.abort();
    assert!(handle.await.unwrap_err().is_cancelled());
    assert!(dropped.load(Ordering::SeqCst));
}

#[super::test]
#[cfg(panic = "unwind")]
async fn panic_drops_the_task_and_keeps_executor_running() {
    let dropped = Arc::new(AtomicBool::new(false));
    let guard = Dropped(dropped.clone());
    let handle = spawn(async move {
        let _guard = guard;
        panic!("task failure");
    });
    assert!(handle.await.unwrap_err().is_panic());
    assert!(dropped.load(Ordering::SeqCst));
    assert_eq!(spawn(async { 42 }).await.unwrap(), 42);
}

#[super::test]
async fn dropping_join_set_aborts_its_tasks() {
    let dropped = Arc::new(AtomicBool::new(false));
    let guard = Dropped(dropped.clone());
    let (started, ready) = oneshot();
    let mut set = JoinSet::new();
    set.spawn(async move {
        let _guard = guard;
        started.send(()).unwrap();
        std::future::pending::<()>().await;
    });
    ready.await.unwrap();
    assert_eq!(set.len(), 1);
    drop(set);
    crate::common_test::periodic_check(|| dropped.load(Ordering::SeqCst), Duration::from_secs(2))
        .await;
}

#[super::test]
async fn join_set_returns_completed_tasks_first() {
    let (send, receive) = oneshot();
    let mut set = JoinSet::new();
    set.spawn(async move { receive.await.unwrap() });
    set.spawn(async { 2 });
    assert_eq!(set.join_next().await.unwrap().unwrap(), 2);
    send.send(1).unwrap();
    assert_eq!(set.join_next().await.unwrap().unwrap(), 1);
    assert!(set.join_next().await.is_none());
    assert!(set.is_empty());
}
