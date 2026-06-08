structure State (σ : Type) (α : Type) where
  run : σ → (α × σ)

namespace State
def map (f : α → β) (s : State σ α) : State σ β :=
  ⟨fun s' => Prod.map f id (s.run s')⟩

def pure (x : α) : State σ α :=
  ⟨fun s => (x, s)⟩

def seq (f : State σ (α → β)) (x : Unit → State σ α) : State σ β :=
  ⟨fun s =>
    let (g, s') := f.run s
    let (a, s'') := (x ()).run s'
    (g a, s'')⟩

def bind (x : State σ α) (f : α → State σ β) : State σ β :=
  ⟨fun s =>
    let (a, s') := x.run s
    (f a).run s'⟩
end State

instance : Functor (State σ) where
  map := State.map

instance : Applicative (State σ) where
  pure := State.pure
  seq := State.seq

instance : Monad (State σ) where
  bind := State.bind

abbrev Stack α := State (List α)

def put (x : α) : Stack α Unit :=
  ⟨fun s => ((), x :: s)⟩

def get [Inhabited α] : Stack α α :=
  ⟨fun s => (s.head!, s.tail)⟩

namespace VirtualMachine
def call : Stack α β → Stack α β := id

def ret (x : α) : Stack α α := pure x

def s_add : Stack Nat Nat := do
  let a ← get
  let b ← get
  ret (a + b)

def test : Stack Nat Nat := do
  put 1
  put 2
  call s_add

#eval test.run []
end VirtualMachine
