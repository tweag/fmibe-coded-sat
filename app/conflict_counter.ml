let value = ref 0

let increment () = incr value
let reset () = value := 0
let get () = !value
