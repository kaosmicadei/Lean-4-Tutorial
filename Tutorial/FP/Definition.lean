def map (f : α → β) : List α → List β
  | [] => []
  | a::as => f a :: map f as

def fold (f : β → α → β) (acc : β) : List α → β
  | [] => acc
  | x :: xs => fold f (f acc x) xs
