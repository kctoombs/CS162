let g1 = 
  (let f1 = ['A, 'C](a: 'A, h: ('C, 'C) => 'C) => 
      ['A](b: 'A) => h(a, b)
  in (f1<num, bool>(5, (x: bool, y:bool) => x && y)))
in g1<bool>(true)
