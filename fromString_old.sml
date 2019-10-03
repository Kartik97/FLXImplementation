fun fromString "" = raise Not_wellformed
      | fromString s = 
        let
          val cons = ["Z","T","F","P","S","ITE","IZ","GTZ"]

          val lst = explode(s) 

          fun tokens ([],tokenList,curr) = if (curr <> "") then curr::tokenList
                                            else tokenList
            | tokens (x::t,tokenList,curr) =
            if (String.str(x) = "(" orelse String.str(x) = "<" orelse String.str(x) = ",")  then
              String.str(x)::tokens(t,tokenList,"")
            else if(String.str(x) = " ") then 
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

        in if(List.length(tokens) <> 0 orelse List.length(term) <> 1 orelse toString(hd(term)) <> s) then raise Not_wellformed
            else hd(term)
        end