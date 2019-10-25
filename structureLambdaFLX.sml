(*structure Flx : FLX =
struct
   Body *)
  exception Not_wellformed
  exception Not_nf
  exception Not_int
  exception Not_welltyped
  datatype lterm = VAR of string      (* variables *)
                   | Z                  (* zero *)
                   | T                  (* true *)
                   | F                  (* false *)
                   | P of lterm         (* Predecessor *)
                   | S of lterm         (* Successor *)
                   | ITE of lterm * lterm * lterm       (* If then else *)
                   | IZ of lterm        (* is zero *)
                   | GTZ of lterm       (* is greater than zero *)
                   | LAMBDA of lterm * lterm    (* lambda x [lterm] *)
                   | APP of lterm * lterm       (* application of lambda terms, i.e. (L M) *)

  val l1 = "LAMBDA x[(P x)]";
  val l2 = "(LAMBDA x[(S (P x))] (P z))"

  fun fromString "" = raise Not_wellformed
    | fromString s = 
      let
        datatype stack =
          TERM of lterm 
          | STR of string

        val lst = explode(s)

        fun tokens ([],tokenList,curr) = if (curr <> "") then curr::tokenList
                                         else tokenList
            | tokens (x::t,tokenList,curr) =
            if (String.str(x) = "(" orelse String.str(x) = "<" orelse String.str(x) = "[")  then
              if(curr <> "") then 
                curr::String.str(x)::tokens(t,tokenList,"")
              else String.str(x)::tokens(t,tokenList,"")
            else if(String.str(x) = " ") then 
              if(curr <> "") then
                curr::tokens(t,tokenList,"")
              else tokens(t,tokenList,"")
            else if(String.str(x) = ")" orelse String.str(x) = ">" orelse String.str(x) = "," orelse String.str(x) = "]") then
              if(curr <> "") then 
                curr::String.str(x)::tokens(t,tokenList,"")
              else String.str(x)::tokens(t,tokenList,"")
            else tokens(t,tokenList,curr^String.str(x))

          fun addSingleBraces ([],singleBrace) = singleBrace
              | addSingleBraces (h::t,singleBrace) = 
                  if(h <> "(" andalso h <> ")" andalso h <> "<" andalso h <> ">" andalso h <> "S" andalso h <> "P"
                  andalso h <> "ITE" andalso h <> "IZ" andalso h <> "GTZ" andalso h <> "," andalso h <> "[" 
                  andalso h <> "]" andalso h <> "LAMBDA" andalso h <> "APP") then
                      "("::h::")"::addSingleBraces(t,singleBrace)
                  else h::addSingleBraces(t,singleBrace)

          val tokenised = addSingleBraces(tokens(lst,[],""),[])  

          fun checkPrevious (STR x) = true
              | checkPrevious (TERM _) = false

          fun findTerm (TERM x) = x
              | findTerm _ = raise Not_wellformed

          fun findStr (STR x) = x
              | findStr _ = raise Not_wellformed

          fun createITE (a::b::c::d::e::f::g::h::t) = 
                if(findStr(b) = "," andalso findStr(d) = "," andalso findStr(f) = "<" andalso findStr(g) = "ITE" andalso findStr(h) = "(" ) then
                  TERM (ITE (findTerm e,findTerm c,findTerm a))::t
                else raise Not_wellformed
              | createITE _ = raise Not_wellformed

          fun createLAMBDA (a::b::c::d::t) =
                if(checkPrevious(a) <> true andalso findStr(b) = "[" andalso checkPrevious(c) <> true andalso findStr(d) = "LAMBDA") then
                  TERM (LAMBDA (findTerm c,findTerm a))::t
                else raise Not_wellformed
              | createLAMBDA _ = raise Not_wellformed

          fun parser ([],stk) = if(List.length(stk) <> 1 orelse checkPrevious(hd stk)) then raise Not_wellformed
                                else findTerm(hd stk) 
              | parser (x::t,stk) = 
                  if (x = ">") then 
                    if((hd t) = ")") then parser(tl t,createITE(stk))
                    else raise Not_wellformed
                  else if(x = "]") then
                    parser(t,createLAMBDA(stk))
                  else if(x <> ")") then parser(t,STR(x)::stk)
                  else if(checkPrevious (hd (stk))) then
                        let val x = findStr(hd stk)
                            val brac = findStr(hd (tl stk))
                        in if(brac <> "(") then raise Not_wellformed
                           else case x of
                                 "T" => parser(t,(TERM T)::(tl (tl stk)))
                                 | "F" => parser(t,(TERM F)::(tl (tl stk)))
                                 | "Z" => parser(t,(TERM Z)::(tl (tl stk)))
                                 | "S" => raise Not_wellformed
                                 | "P" => raise Not_wellformed
                                 | "IZ" => raise Not_wellformed
                                 | "GTZ" => raise Not_wellformed
                                 | "ITE" => raise Not_wellformed
                                 | "LAMBDA" => raise Not_wellformed
                                 | "APP" => raise Not_wellformed
                                 | z => parser(t,(TERM (VAR z))::(tl (tl stk)))
                        end
                  else if(checkPrevious(hd (tl stk))) then
                        let val para = findTerm (hd stk)
                            val cons = findStr(hd (tl stk))
                            val brac = findStr (hd (tl (tl stk)))
                        in if(brac = "(") then
                            case cons of
                            "S" => parser(t,(TERM (S para))::(tl (tl (tl stk))))
                            | "P" => parser(t,(TERM (P para))::(tl (tl (tl stk))))
                            | "IZ" => parser(t,(TERM (IZ para))::(tl (tl (tl stk))))
                            | "GTZ" => parser(t,(TERM (GTZ para))::(tl (tl (tl stk))))
                            | _ => raise Not_wellformed
                           else raise Not_wellformed
                        end
                  else 
                        if(checkPrevious(hd stk) <> true andalso checkPrevious(hd (tl stk)) <> true andalso findStr (hd (tl (tl stk))) = "(") then
                          parser(t,TERM(APP(findTerm(hd (tl stk)),findTerm(hd stk)))::(tl (tl (tl stk))))                   
                        else raise Not_wellformed
      in
        parser(tokenised,[])
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
      | toString (LAMBDA (x1,x2)) = "LAMBDA "^toString(x1)^"["^toString(x2)^"]"
      | toString (APP (x1,x2)) = "("^toString(x1)^" "^toString(x2)^")"

  fun fromInt (x:int) =
      if (x = 0) then Z
      else if(x < 0) then P(fromInt(x+1))
      else S(fromInt(x-1))

  fun toInt t = 
    let
      fun check_int Z = true
          | check_int (S x) = check_int(x)
          | check_int (P x) = check_int(x)
          | check_int _ = false
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
    in 
      if(check_int(t)) then calculate(t)
      else raise Not_int
    end
(*
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
        | repeat (IZ x) = if (checkSuccessor((x)) orelse checkPredeccessor((x))) then F
                        else (IZ (repeat(x)))
        | repeat (GTZ Z) = F
        | repeat (GTZ x) = if (checkSuccessor((x))) then T
                        else if (checkPredeccessor((x))) then F
                        else (GTZ (repeat(x)))

  in

    fun normalize t = 
    let val reduced = repeat(t)
    in if(reduced = t) then reduced
        else normalize reduced
    end

  end *)
(*
end
*)