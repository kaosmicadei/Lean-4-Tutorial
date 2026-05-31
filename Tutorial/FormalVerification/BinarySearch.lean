def Sorted (xs : List Nat) : Prop :=
  ∀ i j : Fin xs.length,
    i < j → j < xs.length → xs.get i ≤ xs.get j
