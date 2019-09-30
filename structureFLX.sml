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







val lst = ["(","S","(","P","Z",")",")"];

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

      (*
      "Z" => if(List.length(stkTerms) <> 0) then raise Not_wellformed
              else [Z]
      | "T" => if(List.length(stkTerms) <> 0) then raise Not_wellformed
              else [T]
      | "F" => if(List.length(stkTerms) <> 0) then raise Not_wellformed
              else [F]
      | "P" => if(List.length(stkTerms) <> 1) then raise Not_wellformed
              else [P(hd(stkTerms))]
      | "S" => if(List.length(stkTerms) <> 1) then raise Not_wellformed
              else [S(hd(stkTerms))]
      | "IZ" => if(List.length(stkTerms) <> 1) then raise Not_wellformed
              else [IZ(hd(stkTerms))]
      | "GTZ" => if(List.length(stkTerms) <> 1) then raise Not_wellformed
              else [GTZ(hd(stkTerms))]
      | "ITE" => if(List.length(stkTerms) <> 3) then raise Not_wellformed
              else [ITE(hd(tl(tl(stkTerms))),hd(tl(stkTerms)),hd(stkTerms))]
      | _ => VAR(token)::stkTerms   *)

fun test ([],stkTokens,stkTerms) = stkTerms
    | test (h::t,stkTokens,stkTerms) = 
        if (h = "<" orelse h = ">") then 
          test (t,stkTokens,stkTerms)
        else if(h <> ")") then 
          test (t,h::stkTokens,stkTerms)
        else
          let fun findPrev ([],stTerms) = raise Not_wellformed
                  | findPrev ("("::tail,stTerms) = test(t,tail,stTerms)
                  | findPrev (head::tail,stTerms) = findPrev(tail,createTerm(head,stTerms))

          in findPrev (stkTokens,stkTerms)
          end   
   (*       if(hd(tl(stkTokens)) = "(") then
            test(t,tl(tl(stkTokens)),createTerm(hd(stkTokens),stkTerms))
          else raise Not_wellformed *)




        (*  if(List.length(stkTerms) = 0) then
            if(hd(stkTokens) = "P" orelse hd(stkTokens) = "S" orelse hd(stkTokens) = "IZ" orelse hd(stkTokens) = "GTZ" orelse hd(stkTokens) = "ITE") then
              raise Not_wellformed
            else if(hd(stkTokens) = "Z") then test (t,tl(stkTokens),Z::stkTerms)
            else if(hd(stkTokens) = "T") then test (t,tl(stkTokens),T::stkTerms)
            else if(hd(stkTokens) = "F") then test (t,tl(stkTokens),F::stkTerms)
            else test (t,tl(stkTokens),VAR(hd(stkTerms))::stkTerms)
          else if(List.length(stkTerms) = 1) then
            if(hd(stkTokens) = "P") then test (t,tl(stkTokens),[P(hd(stkTerms))])
            else if(hd(stkTokens) = "S") then test (t,tl(stkTokens),[S(hd(stkTerms))])
            else if(hd(stkTokens) = "IZ") then test (t,tl(stkTokens),[IZ(hd(stkTerms))])
            else if(hd(stkTokens) = "GTZ") then test (t,tl(stkTokens),[GTZ(hd(stkTerms))])
            else 
          else  *)



































fun fromString "" = raise Not_wellformed
    | fromString s = 
      let
        val cons = ["Z","T","F","P","S","ITE","IZ","GTZ"]
        val lst = explode(s) 
        fun tokens ([],tokenList,curr) = tokenList
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

                
         (*   
            case curr of
              "Z" => "Z"
              | "T" => "T"
              | _ => fromStringItr (t,curr^String.str(x))
         if
          if( x = #")" ) then fromStringItr (t,curr) *)
      in tokenised
      end