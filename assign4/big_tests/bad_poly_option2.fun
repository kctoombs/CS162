type Option['A] = Some 'A | None

let g =
(let map =
  (['A,'C](o: Option<'C>) =>
    (['B](f: ('A) => 'B) =>
      case o of
      | None => None<'B>
      | Some(x) => Some<'B>(f(x))))
  in map<bool,num>(Some<num>(3)))
in g<bool>((x: num) => (x < 1))
