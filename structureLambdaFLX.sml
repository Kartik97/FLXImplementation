(*structure Flx : FLX =
struct
   Body *)
  exception Not_wellformed
  exception Not_nf
  exception Not_int
  exception Not_welltyped
  datatype term = VAR of string (* variable *)
                  | Z           (* zero *)
                  | T           (* true *)
                  | F           (* false *)
                  | P of term   (* Predecessor *)
                  | S of term   (* Successor *)
                  | ITE of term * term * term   (* If then else *)
                  | IZ of term  (* is zero *)
                  | GTZ of term (* is greater than zero *)

  datatype lterm = term
                   | VAR of string      (* variables *)
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

fun isWellTyped t = 
    let
      datatype dict = 
        PAIR of string * int 

      datatype temp = 
        MAP of string * int

      fun findId ([],x) = ~1
        | findId (MAP(s,value)::t,x) = 
          if(s=x) then value else findId(t,x)

      fun insertMap (l,x,v) = if(findId (l,x) = ~1) then MAP(x,v)::l else l

      fun alphaConversion (VAR x,count,temp,new) = if(findId(temp,x) = ~1) then
                                                (VAR (Int.toString(count+1)),count+1,insertMap(temp,x,count+1),insertMap(new,x,count+1))
                                               else (VAR (Int.toString(findId(temp,x))),count,temp,[])
      | alphaConversion (Z,count,temp,new) = (Z,count,temp,new)
      | alphaConversion (T,count,temp,new) = (T,count,temp,new)
      | alphaConversion (F,count,temp,new) = (F,count,temp,new)
      | alphaConversion (S x,count,temp,new) = let
                                                val (t,c,t1,n1) = alphaConversion(x,count,temp,new)
                                              in
                                                (S t,c,t1,new@n1)
                                              end
      | alphaConversion (P x,count,temp,new) = let
                                                val (t,c,t1,n1) = alphaConversion(x,count,temp,new)
                                              in
                                                (P t,c,t1,new@n1)
                                              end
      | alphaConversion (IZ x,count,temp,new) = let
                                                  val (t,c,t1,n1) = alphaConversion(x,count,temp,new)
                                                in
                                                  (IZ t,c,t1,new@n1)
                                                end
      | alphaConversion (GTZ x,count,temp,new) = let
                                                    val (t,c,t1,n1) = alphaConversion(x,count,temp,new)
                                                  in
                                                    (GTZ t,c,t1,new@n1)
                                                  end
      | alphaConversion (ITE (x1,x2,x3),count,temp,new) = let
                                                            val (t1,c1,temp1,new1) = alphaConversion(x1,count,temp,[])
                                                            val (t2,c2,temp2,new2) = alphaConversion(x2,c1,temp,[])
                                                            val (t3,c3,temp3,new3) = alphaConversion(x3,c2,temp,[])
                                                          in
                                                            (ITE (t1,t2,t3),c3,temp@new1@new2@new3,new@new1@new2@new3)
                                                          end
      | alphaConversion (LAMBDA (VAR x,term1),count,temp,new) = if(findId(temp,x) <> ~1) then raise Not_wellformed
                                                                else 
                                                                  let 
                                                                    val temp2 = insertMap(temp,x,count+1)
                                                                    val (t,c,t1,n1) = alphaConversion(term1,count+1,temp2,[])
                                                                  in
                                                                    (LAMBDA (VAR (Int.toString(count+1)),t),c,temp2@n1,MAP(x,count+1)::new@n1)
                                                                  end
      | alphaConversion (APP (x1,x2),count,temp,new) =  let
                                                            val (t1,c1,temp1,new1) = alphaConversion(x1,count,temp,[])
                                                            val (t2,c2,temp2,new2) = alphaConversion(x2,c1,temp,[])
                                                          in
                                                            (APP (t1,t2),c2,temp@new1@new2,new@new1@new2)
                                                          end

      fun find ([],x) = ~1
        | find (PAIR(s,value)::t,x) = 
          if(s=x) then value else find(t,x)

      fun update (PAIR(s,value)::t,x,v,l) = if(s=x) then 
                                        if(value=2 orelse value = v) then PAIR(s,v)::t@l else PAIR(s,value)::t@l
                                   else update(t,x,v,PAIR(s,value)::l)

      fun insert (l,x,v) = if(find (l,x) = ~1) then PAIR(x,v)::l else update(l,x,v,[])

      fun checkVar(VAR x) = x
          | checkVar _ = ""
      (*  int = 1    bool = 0   generic = 2   Not Well typed = ~2*)

      fun checkType (Z,l) = (1,l)
          | checkType (VAR x,l) = (find(insert(l,x,2),x),insert(l,x,2))
          | checkType (T,l) = (0,l)
          | checkType (F,l) = (0,l)
          | checkType (P (VAR x),l) = if (find(insert(l,x,1),x) = 1) then (1,insert(l,x,1)) else (~2,l)
          | checkType (P x,l) =let
                            val (n,L) = checkType (x,l)
                          in
                            if(n = 1 orelse n = 2) then (1,L) else (~2,L)
                          end
          | checkType (S (VAR x),l) = if (find(insert(l,x,1),x) = 1) then (1,insert(l,x,1)) else (~2,l)
          | checkType (S x,l) =let
                            val (n,L) = checkType (x,l)
                          in
                            if(n = 1 orelse n = 2) then (1,L) else (~2,L)
                          end
          | checkType (IZ (VAR x),l) = if (find(insert(l,x,1),x) = 1) then (0,insert(l,x,1)) else (~2,l)
          | checkType (IZ x,l) =let
                            val (n,L) = checkType (x,l)
                          in
                            if(n = 1 orelse n = 2) then (0,L) else (~2,L)
                          end
                          
          | checkType (GTZ (VAR x),l) = if (find(insert(l,x,1),x) = 1) then (0,insert(l,x,1)) else (~2,l)
          | checkType (GTZ x,l) =let
                            val (n,L) = checkType (x,l)
                          in
                            if(n = 1 orelse n = 2) then (0,L) else (~2,L)
                          end
          | checkType (ITE (x1,x2,x3),l) = let
                                        val p1 = if(checkVar(x1) <> "") then insert(l,checkVar x1,0) else l
                                        val p2 = if(checkVar(x2) <> "") then insert(p1,checkVar x2,2) else p1
                                        val p3 = if(checkVar(x3) <> "") then insert(p2,checkVar x3,2) else p2
      (*                                  val (n1,L1) = checkType(x1,p1)
                                        val (n2,L2) = checkType(x2,p2@L1)
                                        val (n3,L3) = checkType(x3,p3@L2)  *)
                                        val (n1,L1) = checkType(x1,p3)
                                        val (n2,L2) = checkType(x2,L1)
                                        val (n3,L3) = checkType(x3,L2)
                                      in
                                        if((n1 = 0 orelse n1 = 2) andalso n2 = n3) then (n3,L3)
                                        else if((n1 = 0 orelse n1 = 2) andalso n2<> ~2 andalso n3 <> ~2) then
                                            if(n2 = 2) then (n3,L3)
                                            else if(n1 = 2) then (n2,L3)
                                            else (~2,p3)
                                        else
                                          (~2,p3)
                                      end
          | checkType (LAMBDA (VAR x,t),l) = checkType(t,l)
          | checkType (LAMBDA (_,_),l) = (~2,l)
          | checkType (APP (LAMBDA (VAR x,t1),t2),l) = let
                                                  val (lmb,lmbList) = checkType(t1,insert(l,x,2))
                                                  val (app,appList) = checkType(t2,lmbList)
                                                in
                                                  if((find(lmbList,x) = app orelse find(lmbList,x) = 2) andalso lmb <> ~2 andalso app <> ~2) then (lmb,appList)
                                                  else (~2,appList)
                                                end
          | checkType(APP (LAMBDA (_,_),_),l) = (~2,l)
          | checkType(APP (t1,t2),l)=let
                                  val (n1,L1) = checkType(t1,l)
                                  val (n2,L2) = checkType(t2,L1)
                                in
                                  if(n1 <> ~2 andalso n2 <> ~2) then (n1,L2) else (~2,L2)
                                end
      val (conv,c,map,nmap) = alphaConversion(t,0,[],[])
      val (n,l) = checkType(conv,[])
  in
      if(n = ~2) then false else true
  end

  datatype temp = 
    MAP of string * int

  fun findId ([],x) = ~1
        | findId (MAP(s,value)::t,x) = 
          if(s=x) then value else findId(t,x)

  fun findStr([],x) = "~1"
      | findStr (MAP(s,value)::t,x) = if(Int.toString(value) = x) then s else findStr(t,x)

  fun insertMap (l,x,v) = if(findId (l,x) = ~1) then MAP(x,v)::l else l

  fun alphaConversion (VAR x,count,temp,new) = if(findId(temp,x) = ~1) then
                                                (VAR (Int.toString(count+1)),count+1,insertMap(temp,x,count+1),insertMap(new,x,count+1))
                                               else (VAR (Int.toString(findId(temp,x))),count,temp,[])
      | alphaConversion (Z,count,temp,new) = (Z,count,temp,new)
      | alphaConversion (T,count,temp,new) = (T,count,temp,new)
      | alphaConversion (F,count,temp,new) = (F,count,temp,new)
      | alphaConversion (S x,count,temp,new) = let
                                                val (t,c,t1,n1) = alphaConversion(x,count,temp,new)
                                              in
                                                (S t,c,t1,new@n1)
                                              end
      | alphaConversion (P x,count,temp,new) = let
                                                val (t,c,t1,n1) = alphaConversion(x,count,temp,new)
                                              in
                                                (P t,c,t1,new@n1)
                                              end
      | alphaConversion (IZ x,count,temp,new) = let
                                                  val (t,c,t1,n1) = alphaConversion(x,count,temp,new)
                                                in
                                                  (IZ t,c,t1,new@n1)
                                                end
      | alphaConversion (GTZ x,count,temp,new) = let
                                                    val (t,c,t1,n1) = alphaConversion(x,count,temp,new)
                                                  in
                                                    (GTZ t,c,t1,new@n1)
                                                  end
      | alphaConversion (ITE (x1,x2,x3),count,temp,new) = let
                                                            val (t1,c1,temp1,new1) = alphaConversion(x1,count,temp,[])
                                                            val (t2,c2,temp2,new2) = alphaConversion(x2,c1,temp,[])
                                                            val (t3,c3,temp3,new3) = alphaConversion(x3,c2,temp,[])
                                                          in
                                                            (ITE (t1,t2,t3),c3,temp@new1@new2@new3,new@new1@new2@new3)
                                                          end
      | alphaConversion (LAMBDA (VAR x,term1),count,temp,new) = if(findId(temp,x) <> ~1) then raise Not_wellformed
                                                                else 
                                                                  let 
                                                                    val temp2 = insertMap(temp,x,count+1)
                                                                    val (t,c,t1,n1) = alphaConversion(term1,count+1,temp2,[])
                                                                  in
                                                                    (LAMBDA (VAR (Int.toString(count+1)),t),c,temp2@n1,MAP(x,count+1)::new@n1)
                                                                  end
      | alphaConversion (APP (x1,x2),count,temp,new) =  let
                                                            val (t1,c1,temp1,new1) = alphaConversion(x1,count,temp,[])
                                                            val (t2,c2,temp2,new2) = alphaConversion(x2,c1,temp,[])
                                                          in
                                                            (APP (t1,t2),c2,temp@new1@new2,new@new1@new2)
                                                          end

   (* SCOPE = 0 LOCAL---------------SCOPE = 1 GLOBAL *)

  fun listMerge ([],n) = n
      | listMerge (m,[]) = m
      | listMerge (h::t,n) = let
                              fun exists (x,[]) = 0
                                  | exists (MAP(var1,id1),MAP(var2,id2)::t) = 
                                      if(var1 = var2 andalso id1 = id2) then 1
                                      else exists(MAP(var1,id1),t)
                            in
                              if(exists(h,n) = 0) then listMerge(t,h::n)
                              else listMerge(t,n)
                            end

  fun alphaRenaming (VAR x,count,scope,mapG,mapL) = if(scope = 1 andalso findId(mapG,x) <> ~1) 
                                                      then (VAR (Int.toString(findId(mapG,x))),mapG,mapL,count)
                                                    else if(scope = 1 andalso findId(mapG,x) = ~1)
                                                      then (VAR (Int.toString(count+1)),insertMap(mapG,x,count+1),mapL,count+1)
                                                    else if(scope = 0 andalso findId(mapL,x) <> ~1)
                                                      then (VAR (Int.toString(findId(mapL,x))),mapG,mapL,count)
                                                    else if(scope = 0 andalso findId(mapG,x) <> ~1)
                                                      then (VAR (Int.toString(findId(mapG,x))),mapG,mapL,count)
                                                    else (VAR (Int.toString(count+1)),insertMap(mapG,x,count+1),mapL,count+1)
      | alphaRenaming (T,count,scope,mapG,mapL) = (T,mapG,mapL,count)
      | alphaRenaming (F,count,scope,mapG,mapL) = (F,mapG,mapL,count)
      | alphaRenaming (Z,count,scope,mapG,mapL) = (Z,mapG,mapL,count)
      | alphaRenaming (P x,count,scope,mapG,mapL) = let
                                                      val (t,mG,mL,c) = alphaRenaming(x,count,scope,mapG,mapL)
                                                    in
                                                      (P t,mG,mL,c)
                                                    end
      | alphaRenaming (S x,count,scope,mapG,mapL) = let
                                                      val (t,mG,mL,c) = alphaRenaming(x,count,scope,mapG,mapL)
                                                    in
                                                      (S t,mG,mL,c)
                                                    end
      | alphaRenaming (IZ x,count,scope,mapG,mapL) = let
                                                        val (t,mG,mL,c) = alphaRenaming(x,count,scope,mapG,mapL)
                                                      in
                                                        (IZ t,mG,mL,c)
                                                      end
      | alphaRenaming (GTZ x,count,scope,mapG,mapL) = let
                                                        val (t,mG,mL,c) = alphaRenaming(x,count,scope,mapG,mapL)
                                                      in
                                                        (GTZ t,mG,mL,c)
                                                      end
      | alphaRenaming (ITE (x1,x2,x3),count,scope,mapG,mapL) = let
                                                                  val (t1,mG1,mL1,c1) = alphaRenaming(x1,count,scope,mapG,mapL)
                                                                  val (t2,mG2,mL2,c2) = alphaRenaming(x2,c1,scope,mG1,mapL)
                                                                  val (t3,mG3,mL3,c3) = alphaRenaming(x3,c2,scope,mG2,mapL)
                                                                  val merge1 = listMerge(mL1,mL2)
                                                                  val merge2 = listMerge(mL3,merge1)
                                                                in
                                                                  (ITE (t1,t2,t3),mG3,merge2,c3)
                                                                end
      | alphaRenaming (APP (x1,x2),count,scope,mapG,mapL) = let
                                                              val (t1,mG1,mL1,c1) = alphaRenaming(x1,count,scope,mapG,mapL)
                                                              val (t2,mG2,mL2,c2) = alphaRenaming(x2,c1,scope,mG1,mapL)
                                                              val merge1 = listMerge(mL1,mL2)
                                                            in
                                                              (APP (t1,t2),mG2,merge1,c2)
                                                            end
      | alphaRenaming (LAMBDA(VAR x1,x2),count,scope,mapG,mapL) = let
                                                                    val (t,mG,mL,c) = if(scope = 0) then
                                                                                        if(findId(mapL,x1) <> ~1) then raise Not_wellformed
                                                                                        else alphaRenaming(x2,count+1,0,mapG,[MAP(x1,count+1)])
                                                                                      else alphaRenaming(x2,count+1,0,mapG,[MAP(x1,count+1)])
                                                                  in
                                                                    (LAMBDA (VAR (Int.toString(count+1)),t),mG,listMerge(mapL,mL),c)
                                                                  end
      | alphaRenaming (LAMBDA (_,_),count,scope,mapG,mapL) = raise Not_wellformed

  fun revert (Z,map) = Z
      | revert (T,map) = T
      | revert (F,map) = F
      | revert (VAR x,map) = VAR (findStr(map,x))
      | revert (S x,map) = S (revert(x,map))
      | revert (P x,map) = P (revert (x,map))
      | revert (IZ x,map) = IZ (revert (x,map))
      | revert (GTZ x,map) = GTZ(revert (x,map))
      | revert (ITE (x1,x2,x3),map) = ITE(revert(x1,map),revert(x2,map),revert(x3,map))
      | revert (LAMBDA(VAR x1,x2),map) = LAMBDA(VAR (findStr(map,x1)),revert(x2,map))
      | revert (APP(x1,x2),map) = APP(revert(x1,map),revert(x2,map))