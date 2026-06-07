/-
A simple workflow can have three states:
* Pending: the workflow has not started yet.
* InProgress: the workflow has started but not completed yet.
* Completed: the workflow has started and completed.

The main invariant for a workflow is that it cannot be completed if it has not
been started. In other words, the following invariant must hold:
> If a workflow is completed, then it must have been started.

We define a `Workflow` as a pair of two boolean values:
* `started` which indicates whether the workflow has started or not.
* `completed` which indicates whether the workflow has completed or not.

It obeys the following truth table:
| started | completed | Safe? |
|---------|-----------|-------|
| false   | false     | true  |
| false   | true      | false |
| true    | false     | true  |
| true    | true      | true  |

This is essentially the truth table for the implication `completed → started`,
which is the invariant we want to use to label a workflow as `Safe`.

> A workflow is `Safe` if it is not completed or if it is completed, then it
> must have been started.

In formal terms:
> ∀ wf : Workflow, Safe wf ↔ (Completed wf → Started wf).

An event that changes the state of the workflow can be either:
* `start` which transitions the workflow from pending to in progress.
* `complete` which transitions the workflow from in progress to completed.

The `step` function takes a workflow and an event and returns the new workflow
after applying the event.
-/

/-
A workflow keeps track of whether it has been started and completed. The main
invariant is that a workflow cannot be completed if it has not been started.
-/
structure Workflow where
  started   : Bool
  completed : Bool

/-
A workflow is `Safe` if it is not completed or if it is completed, then it must
have been started.
-/
def Safe (wf : Workflow) : Prop := wf.completed = true → wf.started = true

/-
An event changes the state of a given workflow.
-/
inductive Event where
  | start    : Event
  | complete : Event

/-
The `step` function update the state of the workflow based on the given event. It
follows the rules:
* If the event is `start`, then the workflow is marked as started.
* If the event is `complete` and the workflow has already been started, then it
  is marked as completed.
* If the event is `complete` and the workflow has not been started, then the
  workflow remains unchanged.
-/
def step : Workflow → Event → Workflow
  | wf, Event.start => { wf with started := true }
  | wf, Event.complete =>
    if wf.started then
      { wf with completed := true }
    else
      wf

/-
The main theorem we want to prove is that the `step` function preserves the
`Safe` invariant.
> If a workflow is `Safe` before an event, then it should still be `Safe` after
> the event as well.
-/
theorem step_preserves_safety (wf : Workflow) (e : Event) :
  Safe wf → Safe (step wf e) := by
  intro h_wf_safe      -- assumes that the workflow is safe before the event
  cases e with
  | start =>           -- if the event is `start`, then the new workflow is safe
    unfold Safe at *
    simp [step]
  | complete =>    -- if the event is `complete`, we consider the `started` state
    unfold Safe at *
    cases h_started : wf.started
    . -- h_started = false → cannot be completed
      cases h_completed : wf.completed
      . -- h_completed = false → safe
        simp [step, h_started]
        exact h_completed
      . -- h_completed = true → unsafe
        simp [step, h_started]
        rw [h_completed]   -- reduces to `true → false` which is a contradiction
        exfalso            -- moves the goal to proving `false`
        have has_started := h_wf_safe h_completed
        rw [has_started] at h_started
        contradiction
    . -- h_started = true → can be completed or not, and both cases are safe
      simp [step, h_started]

/-
With that, we have shown that the `step` function preserves the `Safe` invariant.
This means that if we start with a `Safe` workflow and apply any sequence of
events using the `step` function, the resulting workflow will also be `Safe`.
-/
