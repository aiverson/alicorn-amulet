
open import "amulet/typeable.ml"

let f = Amc.restrict_row

let g: forall ('name: string) -> forall 'base 'value 'record . Amc.row_cons 'base 'name 'value {'record| } => {'record| } -> 'value = fun x -> let (y, _) = Amc.restrict_row @'name x in y

let x = g @"foo" {foo = 1, bar = 2}

external val print: 'a -> () = "print"

let h: forall 'name -> Amc.known_string 'name => () -> () = fun () -> print (Proxy @'name)

let () = h @"baz" ()

external val foo: forall 'name -> Amc.known_string 'name => () = "print"

let () = foo @"quux"
