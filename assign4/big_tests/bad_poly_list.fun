type List['A] = Cons [ hd: 'A, tl:List<'A> ]
              | Nil

rec polyMap:['A,'B](('A) => 'B, List<'A>) => List<'B> =
      ['C, 'B](f: ('C) => 'B, xs:List<'C>) =>
        case xs of
        | Nil => Nil<'B>
        | Cons(r) => Cons<'B>([ hd = f(r.hd), tl = polyMap<'C,'B>(f, r.tl) ])
in
let list = Cons<num>( [ hd = 1, tl = Nil<num> ] ) in
polyMap<num, num>( (n:num) => n+1, list )
