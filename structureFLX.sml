structure structureFLX : FLX =
struct
  (* Body *)
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


fun fromString "" = raise Not_wellformed
    | fromString s = 
      let

        val lst = explode(s)

        fun tokens ([],tokenList,curr) = if (curr <> "") then curr::tokenList
                                         else tokenList
            | tokens (x::t,tokenList,curr) =
            if (String.str(x) = "(" orelse String.str(x) = "<")  then
              String.str(x)::tokens(t,tokenList,"")
            else if(String.str(x) = " ") then 
              if(curr <> "") then
                curr::tokens(t,tokenList,"")
              else tokens(t,tokenList,"")
            else if(String.str(x) = ")" orelse String.str(x) = ">" orelse String.str(x) = ",") then
              if(curr <> "") then 
                curr::String.str(x)::tokens(t,tokenList,"")
              else String.str(x)::tokens(t,tokenList,"")
            else tokens(t,tokenList,curr^String.str(x))

          fun addSingleBraces ([],singleBrace) = singleBrace
              | addSingleBraces (h::t,singleBrace) = 
                  if(h <> "(" andalso h <> ")" andalso h <> "<" andalso h <> ">" andalso h <> "S" andalso h <> "P"
                  andalso h <> "ITE" andalso h <> "IZ" andalso h <> "GTZ" andalso h <> ",") then
                      "("::h::")"::addSingleBraces(t,singleBrace)
                  else h::addSingleBraces(t,singleBrace)

          val tokenised = addSingleBraces(tokens(lst,[],""),[])

          fun checkLength (n,tokenList) = if(List.length(tokenList) = n) then true else false

          fun checkComma ([],0) = true
              | checkComma ([],n) = false
              | checkComma (x::t,n) = if(x = ",") then checkComma(t,n-1) else checkComma(t,n)

          fun checkAngles ([],0) = true
              | checkAngles ([],n) = false
              | checkAngles (x::t,n) = if(x = ",") then checkAngles(t,n-1) else checkAngles(t,n)

          fun parser (x::t) =
              if(x = "(") then 
                let 
                  val (restList,tokenList,termList) = extract_term (t,[],[])
                in
                  case hd(tokenList) of
                    "Z" => if (checkLength(0,termList)) then (restList,Z) else raise Not_wellformed
                    | "T" => if (checkLength(0,termList)) then (restList,T) else raise Not_wellformed
                    | "F" => if (checkLength(0,termList)) then (restList,F) else raise Not_wellformed
                    | "S" => if (checkLength(1,termList)) then (restList,(S (hd termList))) else raise Not_wellformed
                    | "P" => if (checkLength(1,termList)) then (restList,(P (hd termList))) else raise Not_wellformed
                    | "IZ" => if (checkLength(1,termList)) then (restList,(IZ (hd termList))) else raise Not_wellformed
                    | "GTZ" => if (checkLength(1,termList)) then (restList,(GTZ (hd termList))) else raise Not_wellformed
                    | "ITE" => if(checkLength(3,termList) andalso checkComma(tokenList,2) andalso checkAngles(tokenList,2)) then (restList,ITE (hd termList,hd(tl termList),hd(tl(tl termList)))) else raise Not_wellformed
                    | x => if(checkLength(0,termList)) then (restList,VAR x) else raise Not_wellformed
                end
              else raise Not_wellformed
          and extract_term ([],tokenList,termList) = raise Not_wellformed
            | extract_term (x::t,tokenList,termList) =
            if (x = "(") then 
              let 
                val (nextList,term) = parser(x::t)
              in
                extract_term (nextList,tokenList,term::termList)
              end 
            else if(x = ")") then (t,List.rev(tokenList),List.rev(termList))
            else extract_term(t,x::tokenList,termList)

          val (token_list,term) = parser tokenised
      in
          if(List.length(token_list) = 0) then term else raise Not_wellformed
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

end

open structureFLX

val t0 = "(ITE <T,F,F>)"
val t1 = "(ITE <(ITE <(GTZ (S Z)),Z,(IZ (S Z))>),(S (S x)),(S (S (P Z)))>)"
val t2 = "(P (ITE <(S (ITE <T,(P T),(S (S Z))>)),T,(S (P Z))>))"
val t3 = "(P (ITE <(S (ITE <T,(P T),(S (S Z)),T,(S (P Z))>))>))"
val t4 = "(P (ITE <(S (ITE <T,(P T)(S (S Z))>)),T,(S (P Z))>))"
val term1 = ITE (ITE (GTZ (S Z),Z,IZ (S Z)),S (S (VAR "x")),S (S (P Z)))
val term2 = P (ITE (S (ITE (T,P T,S (S Z))),T,S (P Z)))