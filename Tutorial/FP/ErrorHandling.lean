inductive Result (ε : Type) (α : Type) where
  | Err : ε → Result ε α
  | Ok : α → Result ε α

def Result.map (f : α → β) : Result ε α → Result ε β
  | .Err e => .Err e
  | .Ok a => .Ok (f a)

def Result.seq (f : Result ε (α → β)) (x : Unit → Result ε α) : Result ε β :=
  match f, x () with
  | .Err e, _ => .Err e
  | _, .Err e => .Err e
  | .Ok g, .Ok a => .Ok (g a)

def Result.bind (x : Result ε α) (f : α → Result ε β) : Result ε β :=
  match x with
  | .Err e => Err e
  | .Ok a => f a

instance : Functor (Result ε) where
  map := Result.map

instance : Applicative (Result ε) where
  pure := Result.Ok
  seq := Result.seq

instance : Monad (Result ε) where
  bind := Result.bind

#eval (Result.Ok 1 : Result String Nat) >>= (λ_ => Result.Err "failed") >>= (fun x => Result.Ok (x + 1))
