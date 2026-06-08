/-
The goal of this file is to show how formal verification can be used to prove the
correctness of a simple state machine. We will define a workflow model and a `step`
function that updates the state of the workflow based on certain events, and then
prove that the `step` function preserves the safety of the workflow.

For simplicity, our workflow will have two boolean fields: `started` and `completed`.
The `started` field indicates whether the workflow has started or not, and the
`completed` field indicates whether the workflow has completed or not.

A workflow is considered `Safe` if it is not completed or if it is completed,
then it must have been started.

We then define a `step` function that takes a workflow and an event, and updates
the state of the workflow based on the event.

The main theorem we want to prove is that the `step` function preserves the
safety of the workflow. In other words, we want to prove that:

> If a workflow is `Safe` before an event, then it should still be `Safe` after
> the event as well.
-/

/--
A simple workflow can have three states:
* Pending: the workflow has not started yet.
* InProgress: the workflow has started but not completed yet.
* Completed: the workflow has started and completed.

We model the `Workflow` as a pair of two boolean values:
* `started` which indicates whether the workflow has started or not.
* `completed` which indicates whether the workflow has completed or not.

The model maps the states to the following values:
| started | completed | State      |
|---------|-----------|------------|
| false   | false     | Pending    |
| true    | false     | InProgress |
| true    | true      | Completed  |
| false   | true      | _invalid_  |
-/
structure Workflow where
  started   : Bool
  completed : Bool

/--
A workflow is `Safe` if it is not completed or if it is completed, then it must
have been started.

The safety of a workflow follows the truth table:
| started | completed | Safe  |
|---------|-----------|-------|
| false   | false     | true  |
| true    | false     | true  |
| true    | true      | true  |
| false   | true      | false |

This is the truth table of the implication `completed → started`, which is the
definition of the `Safe` invariant.

In formal terms:
> ∀ wf : Workflow, Safe wf ↔ (Completed wf → Started wf).
-/
def Safe (wf : Workflow) : Prop := wf.completed = true → wf.started = true

/--
An event is used to change the state of a given workflow and can be either:
* `start` which transitions the workflow from pending to in progress.
* `complete` which transitions the workflow from in progress to completed.
-/
inductive Event where
  | start    : Event
  | complete : Event

/--
The `step` function updates the state of the workflow based on the given event. It
follows the rules:
* If the event is `start`, then the workflow is marked as started.
* If the event is `complete` and the workflow has already been started, then it
  is marked as completed.
* If the event is `complete` and the workflow has *not* been started, then the
  workflow remains unchanged.
-/
def step : Workflow → Event → Workflow
  | wf, .start => { wf with started := true }
  | wf, .complete =>
    if wf.started then
      { wf with completed := true }
    else
      wf

/-
The main theorem we want to prove is that the `step` function preserves the
`Safe` invariant meaning that if we start with a `Safe` workflow and apply any
sequence of events using the `step` function, the resulting workflow will also
be `Safe`.
-/
theorem step_preserves_safety (wf : Workflow) (e : Event) :
  Safe wf → Safe (step wf e) := by
  intro h_wf_safe      -- assumes that the workflow is safe before the event
  cases e with
  | start =>           -- if the event is `start`, then the new workflow is safe
    simp [Safe, step]
  | complete =>    -- if the event is `complete`, we consider the `started` state
    simp [Safe] at *
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
This concludes our goal. We have successfully proved that the `step` function
preserves the workflow's safety.
-/
