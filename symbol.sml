signature SYMBOL =
sig
  eqtype symbol
  val symbol : string -> symbol
  val name : symbol -> string
  type 'a table
  val empty : 'a table
  val remove : symbol * 'a table  -> 'a table * 'a
  val enter : symbol * 'a * 'a table  -> 'a table
  val enter' : (symbol * 'a) list * 'a table -> 'a table
  val lookup : symbol * 'a table  -> 'a option
  val listItems : 'a table -> 'a list
  val map : ('a -> 'b) -> 'a table -> 'b table
  val compare     : symbol * symbol -> order

end

structure Symbol :> SYMBOL =
struct

  type symbol = string * int

  structure H = HashTable

  exception Symbol
  val nextsym   = ref 0
  val sizeHint  = 128
  val hashtable : (string,int) H.hash_table = 
		H.mkTable(HashString.hashString, op = ) (sizeHint,Symbol)
  
  fun symbol name =
      case H.find hashtable name
       of SOME i => (name,i)
        | NONE => let val i = !nextsym
	           in nextsym := i+1;
		      H.insert hashtable (name,i);
		      (name,i)
		  end

  fun name(s,n) = s

  structure Table = IntMapTable (type key = symbol
				 fun getInt(s,n) = n)

  type 'a table= 'a Table.table
  val empty = Table.empty

  val listItems = Table.listItems
  val map = Table.map

  fun enter (s,v,t)  = Table.enter (t,s,v)
  fun enter' (lst,t) = foldl (fn ((s,v),t) => Table.enter (t,s,v)) t lst
  fun lookup (s,t)   = Table.look (t,s)
  fun remove (s,t)   = Table.remove (t,s)

  fun compare ((_,s1),(_,s2)) = Int.compare (s1,s2)
end
