
let rec
  isort_int : int list -> int list =
    function
      | [] -> []
      | x :: xs -> insert_int x (isort_int xs)
  and
  insert_int (e : int) : int list -> int list =
    function
      | [] -> [e]
      | x :: xs when e <= x -> e :: x :: xs
      | x :: xs -> x :: insert_int e xs

let isort (comp : 'a -> 'a -> bool) : 'a list -> 'a list =
  let rec insert (e : 'a) : 'a list -> 'a list =
    function
      | [] -> [e]
      | x :: xs when comp e x -> e :: x :: xs
      | x :: xs -> x :: insert e xs in
  let rec isort_ : 'a list -> 'a list =
    function
      | [] -> []
      | x :: xs -> insert x (isort_ xs) in isort_

let qsort (comp : 'a -> 'a -> bool) : 'a list -> 'a list =
  let partition (e : 'a) : 'a list -> 'a list * 'a list =
    let rec part : 'a list -> 'a list * 'a list =
      function
        | [] -> [] , []
        | x :: xs when comp x e -> (fun (l , r) -> (x :: l) , r) (part xs)
        | x :: xs -> (fun (l , r) -> l , (x :: r)) (part xs) in part in
  let rec qsort' : 'a list -> 'a list =
    function
      | [] -> []
      | x :: xs -> (fun (l , r) -> qsort' l @ [x] @ qsort' r) (partition x xs)
    in qsort'

let msort (comp : 'a -> 'a -> bool) (xs : 'a list) : 'a list =
  let rec merge (ls : 'a list) (rs : 'a list) : 'a list =
    match ls , rs with
      | [] , r -> r
      | l , [] -> l
      | (l :: ls) , (r :: rs) when comp l r -> l :: merge ls (r :: rs)
      | ls , (r :: rs) -> r :: merge ls rs in
  let rec msort' : 'a list list -> 'a list list =
    function
      | [] -> []
      | [x] -> [x]
      | (x :: x' :: xs) -> merge x x' :: msort' xs in
  let rec msort'' : 'a list list -> 'a list =
    function
      | [] -> []
      | [x] -> x
      | l -> msort'' (msort' l) in
  msort'' (List.map (fun a -> [a]) xs)

