// Copyright (c) Sean Lawlor
//
// This source code is licensed under both the MIT license found in the
// LICENSE-MIT file in the root directory of this source tree.

//! Represents an actor registry.
//!
//! It allows unique naming of actors via `String`
//! so it works more or less like an Erlang `atom()`
//!
//! Actors are automatically registered into the global registry, if they
//! provide a name, upon construction. Actors are also
//! automatically unenrolled from the registry upon being dropped, therefore freeing
//! the name for subsequent registration.
//!
//! You can then retrieve actors by name with [where_is]. Note: this
//! function only returns the [ActorCell] reference to the actor, it
//! additionally requires knowledge of the [crate::Actor] in order
//! to send messages to it (since you need to know the message type)
//! or agents will runtime panic on message reception, and supervision
//! processes would need to restart the actors.
//!
//! ## Examples
//!
//! **Basic actor retrieval**
//! ```rust
//! async fn test() {
//!     let maybe_actor = ractor::registry::where_is("my_actor".to_string());
//!     if let Some(actor) = maybe_actor {
//!         // send a message, or interact with the actor
//!         // but you'll need to know the actor's strong type
//!     }
//! }
//! ```
//!
//! **Full example**
//!
//! ```rust
//! use ractor::registry;
//! use ractor::Actor;
//! use ractor::ActorProcessingErr;
//! use ractor::ActorRef;
//!
//! struct ExampleActor;
//!
//! #[cfg_attr(feature = "async-trait", ractor::async_trait)]
//! impl Actor for ExampleActor {
//!     type Msg = ();
//!     type State = ();
//!     type Arguments = ();
//!
//!     async fn pre_start(
//!         &self,
//!         _myself: ActorRef<Self::Msg>,
//!         _args: Self::Arguments,
//!     ) -> Result<Self::State, ActorProcessingErr> {
//!         println!("Starting");
//!         Ok(())
//!     }
//! }
//!
//! #[tokio::main]
//! async fn main() {
//!     let (actor, handle) = Actor::spawn(Some("my_actor".to_string()), ExampleActor, ())
//!         .await
//!         .expect("Failed to startup dummy actor");
//!
//!     // Retrieve the actor by name from the registry
//!     let who: ActorRef<()> = registry::where_is("my_actor".to_string())
//!         .expect("Failed to find actor")
//!         .into();
//!     who.cast(()).expect("Failed to send message");
//!
//!     // wait for actor exit
//!     actor.stop(None);
//!     handle.await.unwrap();
//!
//!     // Automatically removed from the registry upon shutdown
//!     assert!(registry::where_is("my_actor".to_string()).is_none());
//! }
//! ```

use std::sync::Arc;

use dashmap::mapref::entry::Entry::Occupied;
use dashmap::mapref::entry::Entry::Vacant;
use dashmap::DashMap;
use once_cell::sync::OnceCell;

use crate::ActorCell;
use crate::ActorName;

#[cfg(feature = "cluster")]
pub mod pid_registry;
#[cfg(feature = "cluster")]
pub use pid_registry::get_all_pids;
#[cfg(feature = "cluster")]
pub use pid_registry::where_is_pid;
#[cfg(feature = "cluster")]
pub use pid_registry::PidLifecycleEvent;

#[cfg(test)]
mod tests;

/// Errors involving the [crate::registry]'s actor registry
#[derive(Debug)]
pub enum ActorRegistryErr {
    /// Actor already registered
    AlreadyRegistered(ActorName),
}

/// The name'd actor registry
static ACTOR_REGISTRY: OnceCell<Arc<DashMap<ActorName, ActorCell>>> = OnceCell::new();

/// Retrieve the named actor registry handle
fn get_actor_registry<'a>() -> &'a Arc<DashMap<ActorName, ActorCell>> {
    ACTOR_REGISTRY.get_or_init(|| Arc::new(DashMap::new()))
}

/// Put an actor into the registry
pub(crate) fn register(name: ActorName, actor: ActorCell) -> Result<(), ActorRegistryErr> {
    match get_actor_registry().entry(name.clone()) {
        Occupied(_) => Err(ActorRegistryErr::AlreadyRegistered(name)),
        Vacant(vacancy) => {
            vacancy.insert(actor);
            Ok(())
        }
    }
}

/// Remove an actor from the registry given it's actor name
pub(crate) fn unregister(name: ActorName) {
    if let Some(reg) = ACTOR_REGISTRY.get() {
        let _ = reg.remove(&name);
    }
}

/// Try and retrieve an actor from the registry
///
/// * `name` - The name of the [ActorCell] to try and retrieve
///
/// Returns: Some(actor) on successful identification of an actor, None if
/// actor not registered
pub fn where_is(name: ActorName) -> Option<ActorCell> {
    let reg = get_actor_registry();
    reg.get(&name).map(|v| v.value().clone())
}

/// Returns a list of names that have been registered
///
/// Returns: A [`Vec<String>`] of actor names which are registered
/// currently
pub fn registered() -> Vec<ActorName> {
    let reg = get_actor_registry();
    reg.iter().map(|kvp| kvp.key().clone()).collect::<Vec<_>>()
}
