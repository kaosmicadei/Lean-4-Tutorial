def map (f : α → β) : List α → List β
  | [] => []
  | a::as => f a :: map f as

#eval map (fun x => x + 1) [1, 2, 3]

def fold (f : β → α → β) (acc : β) : List α → β
  | [] => acc
  | x :: xs => fold f (f acc x) xs

#eval fold (fun acc x => acc + x) 0 [1, 2, 3]


/--
Different then `map` and `fold` functions that have structural reductions on the
list, the binary search doesn't show an explicit reduction in the list size.
That means the compiler cannot "guess" the function will terminate. To fix this,
we need to manually specify the termination measure, and prove that it decreases
in each recursive call.
-/
def binarySearch (xs : List Nat) (x : Nat) : Option Nat :=
  if xs.length = 0 then  -- necessary for the termination proof, h†:¬x.length=0
    none
  else
    let mid := xs.length / 2
    match xs[mid]? with
    | none => none
    | some y =>
      if x < y then
        binarySearch (xs.take mid) x
      else if x > y then
        binarySearch (xs.drop (mid+1)) x
      else
        some mid
termination_by xs.length
decreasing_by
  . simp [List.length_take]  -- x < y case
    omega
  . simp [List.length_drop]  -- x > y case
    omega

#eval binarySearch [1, 2, 3, 4, 5] 3
#eval binarySearch [1, 2, 3, 4, 5] 6

/--
We can also write the binary search in a way that doesn't require termination
proof, by using `partial` keyword. However, the whole idea is to write safe
functions that are guaranteed to terminate, so the use of `partial` is usually
left for special cases where termination is not obvious, and we don't want to
spend time proving it.
-/
partial def binarySearch' : List Nat → Nat → Option Nat
  | [], _ => none
  | xs, x =>
    let mid := xs.length / 2
    match xs[mid]? with
    | none => none
    | some y =>
      if x < y then
        binarySearch' (xs.take mid) x
      else if x > y then
        binarySearch' (xs.drop (mid + 1)) x
      else
        some mid

#eval binarySearch' [1, 2, 3, 4, 5] 3
#eval binarySearch' [1, 2, 3, 4, 5] 6
