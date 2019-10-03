exception Not_wellformed
exception Not_nf
exception Not_int
datatype term = VAR of string (* variable *)
                | Z           (* zero *)
                | T           (* true *)
                | F           (* false *)
                | P of term   (* Predecessor *)
                | S of term   (* Successor *)
                | ITE of term * term * term   (* If then else *)
                | IZ of term  (* is zero *)
                | GTZ of term (* is greater than zero *)

val t1 = "(ITE <(ITE <(GTZ (S Z)),Z,(IZ (S Z))>),(S (S x)),(S (S (P Z)))>)"

fun fromString "" = raise Not_wellformed
    | fromString s = 
      let
        val cons = ["Z","T","F","P","S","ITE","IZ","GTZ"]

        val lst = explode(s) 

        fun tokens ([],tokenList,curr) = if (curr <> "") then curr::tokenList
                                          else tokenList
          | tokens (x::t,tokenList,curr) =
          if (String.str(x) = "(" orelse String.str(x) = "<")  then
            String.str(x)::tokens(t,tokenList,"")
          else if(String.str(x) = " " orelse String.str(x) = ",") then 
            if(curr <> "") then
              curr::tokens(t,tokenList,"")
            else tokens(t,tokenList,"")
          else if(String.str(x) = ")" orelse String.str(x) = ">") then
            if(curr <> "") then 
              curr::String.str(x)::tokens(t,tokenList,"")
            else String.str(x)::tokens(t,tokenList,"")
          else tokens(t,tokenList,curr^String.str(x))

        fun addSingleBraces ([],singleBrace) = singleBrace
            | addSingleBraces (h::t,singleBrace) = 
                if(h <> "(" andalso h <> ")" andalso h <> "<" andalso h <> ">" andalso h <> "S" andalso h <> "P" andalso h <> "ITE" andalso h <> "IZ" andalso h <> "GTZ") then
                  "("::h::")"::addSingleBraces(t,singleBrace)
                else h::addSingleBraces(t,singleBrace)

        val tokenised = addSingleBraces(tokens(lst,[],""),[])

        fun createTerm (token,stkTerms) =
            case token of
              "Z" => Z::stkTerms
              | "T" => T::stkTerms
              | "F" => F::stkTerms
              | "P" => if(List.length(stkTerms) < 1) then raise Not_wellformed
                      else P(hd(stkTerms))::tl(stkTerms)
              | "S" => if(List.length(stkTerms) < 1) then raise Not_wellformed
                      else S(hd(stkTerms))::tl(stkTerms)
              | "IZ" => if(List.length(stkTerms) < 1) then raise Not_wellformed
                      else IZ(hd(stkTerms))::tl(stkTerms)
              | "GTZ" => if(List.length(stkTerms) < 1) then raise Not_wellformed
                      else GTZ(hd(stkTerms))::tl(stkTerms)
              | "ITE" => if(List.length(stkTerms) < 3) then raise Not_wellformed
                      else ITE(hd(tl(tl(stkTerms))),hd(tl(stkTerms)),hd(stkTerms))::tl(tl(tl(stkTerms)))
              | _ => VAR(token)::stkTerms

        fun parser ([],stkTokens,stkTerms) = (stkTokens,stkTerms)
            | parser (h::t,stkTokens,stkTerms) = 
                if (h = "<" orelse h = ">") then 
                  parser (t,stkTokens,stkTerms)
                else if(h <> ")") then 
                  parser (t,h::stkTokens,stkTerms)
                else
                  let fun findPrev ([],stTerms) = raise Not_wellformed
                          | findPrev ("("::tail,stTerms) = parser(t,tail,stTerms)
                          | findPrev (head::tail,stTerms) = findPrev(tail,createTerm(head,stTerms))
                  in findPrev (stkTokens,stkTerms)
                  end   

        val (tokens,term) = parser(tokenised,[],[])

      in if(List.length(tokens) <> 0 orelse List.length(term) <> 1) then raise Not_wellformed
          else hd(term)
      end

fun toString (VAR str) = str
    | toString Z = "Z"
    | toString T = "T"
    | toString F = "F"
    | toString (P (x)) = "(P "^toString(x)^")"
    | toString (S (x)) = "(S "^toString(x)^")"
    | toString (IZ (x)) = "(IZ "^toString(x)^")"
    | toString (GTZ (x)) = "(GTZ "^toString(x)^")"
    | toString (ITE (x1,x2,x3)) = "(ITE <"^toString(x1)^","^toString(x2)^","^toString(x3)^">)" 

fun fromInt (x:int) =
    if (x = 0) then Z
    else if(x < 0) then P(fromInt(x+1))
    else S(fromInt(x-1))

fun toInt t = 
  let 
    fun positive (S Z) = 1
        | positive (S x) = positive(x)+1
        | positive (P x) = raise Not_nf
        | positive _ = raise Not_int
    fun negative (P Z) = ~1
        | negative (P x) = negative(x)-1
        | negative (S x) = raise Not_nf
        | negative _ = raise Not_int 
    fun calculate (P x) = negative (P x)
        | calculate (S x) = positive (S x)
        | calculate Z = 0
        | calculate _ = raise Not_int
  in calculate(t) 
  end

local
  fun checkSuccessor Z = true
      | checkSuccessor (S x) = checkSuccessor x
      | checkSuccessor _ = false

  fun checkPredeccessor Z = true
      | checkPredeccessor (P x) = checkPredeccessor x
      | checkPredeccessor _ = false

  fun repeat (VAR str) = VAR str
      | repeat Z = Z
      | repeat T = T
      | repeat F = F
      | repeat (P (S x)) = repeat x
      | repeat (S (P x)) = repeat x
      | repeat (P x) = P(repeat x)
      | repeat (S x) = S(repeat x)
      | repeat (ITE (T,y,z)) = repeat y
      | repeat (ITE (F,y,z)) = repeat z
      | repeat (ITE (x,y,z)) = if (repeat(y) = repeat(z)) then repeat (y)
                             else if (repeat(x) = T) then repeat(y)
                             else if (repeat(x) = F) then repeat(z) 
                             else ITE(repeat(x),repeat(y),repeat(z))
      | repeat (IZ Z) = T
      | repeat (IZ x) = if (checkSuccessor(repeat(x)) orelse checkPredeccessor(repeat(x))) then F
                      else (IZ (repeat(x)))
      | repeat (GTZ Z) = F
      | repeat (GTZ x) = if (checkSuccessor(repeat(x))) then T
                      else if (checkPredeccessor(repeat(x))) then F
                      else (GTZ (repeat(x)))

in
  fun normalize t = 
  let val reduced = repeat(t)
  in if(reduced = t) then reduced
      else normalize reduced
  end

end