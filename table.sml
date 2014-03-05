signature TABLE = 
sig
   type key

   type 'a table
   val empty       : 'a table
   val enter       : 'a table * key * 'a -> 'a table
   val look        : 'a table * key -> 'a option
   val find        : 'a table * key -> 'a option
   val remove      : 'a table * key -> 'a table * 'a
   val numItems    : 'a table -> int
   val listKeys    : 'a table -> int list
   val listItems   : 'a table -> 'a list
   val listItemsi  : 'a table -> (int * 'a) list
   val map         : ('a -> 'b) -> 'a table -> 'b table
end


functor IntMapTable (type key
		     val getInt: key -> int) : TABLE =

struct

  type key = key

  structure H = RedBlackMapFn (struct
			       type ord_key = int
			       val compare = Int.compare
			       end)
					    
  type 'a table = 'a H.map
  val empty = H.empty
  fun enter (t, k, a) = H.insert(t, getInt k, a)
  fun look(t, k) = H.find(t,getInt k)
  val find = look
  fun remove(t, k) = H.remove(t,getInt k)
  fun numItems(t) = H.numItems(t)
  fun listKeys (t) = H.listKeys (t)
  fun listItems (t) = H.listItems (t)
  fun listItemsi (t) = H.listItemsi (t)
  fun map(f) = H.map (f)
end
