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
      (*------------------------ALPHA RENAMING------------------------------*)

      datatype temp = 
        MAP of string * int

      fun findId ([],x) = ~1
            | findId (MAP(s,value)::t,x) = 
              if(s=x) then value else findId(t,x)

      fun findStr([],x) = "~1"
          | findStr (MAP(s,value)::t,x) = if(Int.toString(value) = x) then s else findStr(t,x)

      fun insertMap (l,x,v) = if(findId (l,x) = ~1) then MAP(x,v)::l else l

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
                                                                                            else alphaRenaming(x2,count+1,0,mapG,MAP(x1,count+1)::mapL)
                                                                                          else alphaRenaming(x2,count+1,0,mapG,[MAP(x1,count+1)])
                                                                      in
                                                                        (LAMBDA (VAR (Int.toString(count+1)),t),mG,listMerge(mapL,mL),c)
                                                                      end
          | alphaRenaming (LAMBDA (_,_),count,scope,mapG,mapL) = raise Not_wellformed


      (*-------------------TC------------------------------------------------*)
      datatype dict = 
        PAIR of string * int

      fun find ([],x) = ~1
        | find (PAIR(s,value)::t,x) = 
          if(s=x) then value else find(t,x)

      fun update (PAIR(s,value)::t,x,v,l) = if(s=x) then PAIR(s,v)::t@l
                                            else update(t,x,v,PAIR(s,value)::l)

      fun insert (l,x,v) = PAIR(x,v)::l

      fun checkVar(VAR x) = x
          | checkVar _ = ""

      fun checkLambda (LAMBDA (VAR x1,x2)) = (x1,x2)
          | checkLambda _ = ("",Z)
 
      fun substitute (VAR z,x,t2) = if(z=x) then t2 else (VAR z)
        | substitute (Z,x,t2) = Z
        | substitute (T,x,t2) = T
        | substitute (F,x,t2) = F
        | substitute (P z,x,t2) = P (substitute (z,x,t2))
        | substitute (S z,x,t2) = S (substitute (z,x,t2))
        | substitute (IZ z,x,t2) = IZ (substitute (z,x,t2))
        | substitute (GTZ z,x,t2) = GTZ (substitute (z,x,t2))
        | substitute (ITE (z1,z2,z3),x,t2) = ITE (substitute(z1,x,t2),substitute(z2,x,t2),substitute(z3,x,t2))
        | substitute (LAMBDA (VAR z,t1),x,t2) = LAMBDA(VAR z,substitute(t1,x,t2))
        | substitute (APP (z1,z2),x,t2) = APP(substitute(z1,x,t2),substitute(z2,x,t2))

      (*        bool = 0    int = 1   fn = 2    generic = 3 (int/bool)   Not Well typed = ~2          *)

      fun checkType (Z,l) = (1,~1,~1,l,Z)
          | checkType (T,l) = (0,~1,~1,l,Z)
          | checkType (F,l) = (0,~1,~1,l,Z)
          | checkType (VAR x,l) = if(find(l,x) = ~1) then (3,~1,~1,insert(l,x,3),Z)
                                  else (find(l,x),~1,~1,l,Z)
          | checkType (P (VAR x),l) = if(find(l,x) = ~1) then (1,~1,~1,insert(l,x,1),Z)
                                      else if(find(l,x) = 1) then (1,~1,~1,l,Z)
                                      else if(find(l,x) = 3) then (1,~1,~1,update(l,x,1,[]),Z)
                                      else (~2,~1,~1,l,Z)
          | checkType (P x,l) = let
                                  val (typ,i1,i2,L,p) = checkType (x,l)
                                in
                                  if(typ = 1 orelse typ = 3) then (1,~1,~1,L,Z) else (~2,~1,~1,L,Z)
                                end
          | checkType (S (VAR x),l) = if(find(l,x) = ~1) then (1,~1,~1,insert(l,x,1),Z)
                                      else if(find(l,x) = 1) then (1,~1,~1,l,Z)
                                      else if(find(l,x) = 3) then (1,~1,~1,update(l,x,1,[]),Z)
                                      else (~2,~1,~1,l,Z)
          | checkType (S x,l) = let
                                  val (typ,i1,i2,L,p) = checkType (x,l)
                                in
                                  if(typ = 1 orelse typ = 3) then (1,~1,~1,L,Z) else (~2,~1,~1,L,Z)
                                end
          | checkType (IZ (VAR x),l) = if(find(l,x) = ~1) then (0,~1,~1,insert(l,x,1),Z)
                                      else if(find(l,x) = 1) then (0,~1,~1,l,Z)
                                      else if(find(l,x) = 3) then (0,~1,~1,update(l,x,1,[]),Z)
                                      else (~2,~1,~1,l,Z) 
          | checkType (IZ x,l) = let
                                  val (typ,i1,i2,L,p) = checkType (x,l)
                                in
                                  if(typ = 1 orelse typ = 3) then (0,~1,~1,L,Z) else (~2,~1,~1,L,Z)
                                end
          | checkType (GTZ (VAR x),l) = if(find(l,x) = ~1) then (0,~1,~1,insert(l,x,1),Z)
                                      else if(find(l,x) = 1) then (0,~1,~1,l,Z)
                                      else if(find(l,x) = 3) then (0,~1,~1,update(l,x,1,[]),Z)
                                      else (~2,~1,~1,l,Z) 
          | checkType (GTZ x,l) = let
                                    val (typ,i1,i2,L,p) = checkType (x,l)
                                  in
                                    if(typ = 1 orelse typ = 3) then (0,~1,~1,L,Z) else (~2,~1,~1,L,Z)
                                  end
          | checkType (ITE (x1,x2,x3),l) = let
                                              val p1 = if(checkVar(x1) <> "" andalso find(l,checkVar(x1)) = ~1) then 
                                                        insert(l,checkVar x1,0) 
                                                      else l
                                              val p2 = if(checkVar(x2) <> "" andalso find(p1,checkVar(x2)) = ~1) then 
                                                        insert(p1,checkVar x2,3) 
                                                      else p1
                                              val p3 = if(checkVar(x3) <> "" andalso find(p2,checkVar(x3)) = ~1) then 
                                                        insert(p2,checkVar x3,3) 
                                                      else p2
                                              val (typ1,i11,i12,L1,p1) = checkType (x1,p3)
                                              val (typ2,i21,i22,L2,p2) = checkType (x2,L1)
                                              val (typ3,i31,i32,L3,p3) = checkType (x3,L2)
                                            in
                                              if(typ1 = 0 orelse typ1 = 3) then
                                                if(typ2 = 2 orelse typ3 = 2) then (~2,~1,~1,L3,Z) 
                                                else if(typ2 = typ3) then (typ2,~1,~1,L3,Z)
                                                else if(typ2 <> 3 andalso typ3 <> 3) then (~2,~1,~1,L3,Z) 
                                                else if(typ2 = 3) then
                                                  if(checkVar(x2) <> "") then 
                                                    if(find(L3,checkVar(x2)) = 3) then (typ3,~1,~1,update(L3,checkVar(x2),typ3,[]),Z)
                                                    else (~2,~1,~1,L3,Z)
                                                  else (typ3,~1,~1,L3,Z)
                                                else if(checkVar(x3) <> "") then 
                                                  if(find(L3,checkVar(x3)) = 3) then (typ2,~1,~1,update(L3,checkVar(x3),typ2,[]),Z)
                                                  else (~2,~1,~1,L3,Z)
                                                else (typ2,~1,~1,L3,Z)
                                              else (~2,~1,~1,L3,Z) 
                                            end
          | checkType (LAMBDA (VAR x1,x2),l) = let
                                                val (typ,i1,i2,L,p) = if(find(l,x1) = ~1) then checkType (x2,insert(l,x1,3))  
                                                                    else checkType (x2,l)
                                              in
                                                if(typ = 2) then (2,find(L,x1),i2,L,Z)
                                                else if(typ <> ~2) then (2,find(L,x1),typ,L,Z)
                                                else (~2,~1,~1,L,Z)
                                              end
          | checkType (APP (LAMBDA (VAR x1,x2),x3),l) = let
                                                          val (typ1,t3,i4,L2,p2) = checkType(x3,l)
                                                          val t = substitute(x2,x1,x3)
                                                          val (typ,i1,i2,L1,p1) = checkType (t,L2)
                                                        in
                                                          if(typ <> ~2 andalso typ1 <> ~2) then
                                                            (typ,i1,i2,L1,t)
                                                          else (~2,~1,~1,L1,Z)
                                             (*         val (typ2,i21,i22,L2,p1) = checkType (x3,l)
                                                      val (typ1,i11,i12,L1,p2) = if(find(l,x1) = ~1) then
                                                                                  if(typ2 <> 2) then
                                                                                    checkType (x2,insert(L2,x1,typ2))
                                                                                  else checkType (x2,insert(L2,x1,i22))
                                                                                else checkType(x2,L2)
                                                    in
                                                      if(typ2 = ~2 orelse typ1 = ~2) then (~2,~1,~1,L1,Z)
                                                      else (typ1,i11,i12,L1,substitute(x2,x1,x3))   *)
                                                    end
          | checkType (APP(APP(x1,x2),x3),l) = let
                                                val (typ1,i11,i12,L1,p1) = checkType (APP(x1,x2),l)
                                                val (var,ext) = if(typ1 <> 2) then ("",Z) else checkLambda(p1)
                                                val (typ2,i1,i2,L2,p2) = if(var <> "") then checkType(substitute(ext,var,x3),L1)
                                                                        else (~2,~1,~1,L1,Z)
                                                val (typ3,i3,i4,L3,p3) = checkType(x3,L2)
                                              in if(typ2 <> ~2 andalso typ3 <> ~2) then
                                                (typ2,i1,i2,L3,substitute(ext,var,x3))
                                              else (~2,~1,~1,L3,Z)
                                     (*     val (typ1,i11,i12,L1,p1) = checkType (APP(x1,x2),l)
                                          val (typ2,i21,i22,L2,p2) = checkType (x3,L1)
                                          val (var,ext) = if(typ1 <> 2) then ("",Z) else checkLambda(p1)
                                          val applied = if(var <> "") then substitute(ext,var,x3) else Z
                                          val (str,extracted) = checkLambda(applied)
                                        in
                                          if(typ1 <> 2) then (~2,~1,~1,L2,Z)
                                          else if (typ2 <> 2) then 
                                            if(str <> "") then 
                                              if(i11 = typ2 orelse i11=3 orelse typ2 = 3) then (2,find(L2,str),i12,L2,extracted)
                                              else (~2,~1,~1,L2,Z)
                                            else if(i11 = typ2 orelse i11=3 orelse typ2=3) then (i12,~1,~1,L2,Z)
                                                else (~2,~1,~1,L2,Z)
                                          else if(str <> "") then
                                            if(i11 = i22 orelse i11=3 orelse i22 = 3) then (2,find(L2,str),i12,L2,extracted)
                                              else (~2,~1,~1,L2,Z)
                                          else if(i11 = i22 orelse i11=3 orelse i22=3) then (i12,~1,~1,L2,Z)
                                                else (~2,~1,~1,L2,Z)  *)
                                        end
          | checkType (APP(_,_),l) = (~2,~1,~1,l,Z)
          | checkType (LAMBDA(_,_),l) = (~2,~1,~1,l,Z)

      val (conv,mapG,mapL,count) = alphaRenaming(t,0,1,[],[])
      val (n,i1,i2,l,t) = checkType(conv,[])
  in
       if(n = ~2) then false else true 
  (*    (n,i1,i2,l,t)   *)
  end


  fun betanf t = 
    let
      (*------------------------ALPHA RENAMING------------------------------*)

      datatype temp = 
        MAP of string * int

      fun findId ([],x) = ~1
            | findId (MAP(s,value)::t,x) = 
              if(s=x) then value else findId(t,x)

      fun findStr([],x) = "~1"
          | findStr (MAP(s,value)::t,x) = if(Int.toString(value) = x) then s else findStr(t,x)

      fun insertMap (l,x,v) = if(findId (l,x) = ~1) then MAP(x,v)::l else l

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
                                                                                            else alphaRenaming(x2,count+1,0,mapG,MAP(x1,count+1)::mapL)
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

  (*-----------------------------------NORMALIZATION-----------------------------------------------*)
    fun checkSuccessor Z = true
        | checkSuccessor (S x) = checkSuccessor x
        | checkSuccessor _ = false

    fun checkPredeccessor Z = true
        | checkPredeccessor (P x) = checkPredeccessor x
        | checkPredeccessor _ = false

    fun substitute (VAR z,x,t2) = if(z=x) then t2 else (VAR z)
        | substitute (Z,x,t2) = Z
        | substitute (T,x,t2) = T
        | substitute (F,x,t2) = F
        | substitute (P z,x,t2) = P (substitute (z,x,t2))
        | substitute (S z,x,t2) = S (substitute (z,x,t2))
        | substitute (IZ z,x,t2) = IZ (substitute (z,x,t2))
        | substitute (GTZ z,x,t2) = GTZ (substitute (z,x,t2))
        | substitute (ITE (z1,z2,z3),x,t2) = ITE (substitute(z1,x,t2),substitute(z2,x,t2),substitute(z3,x,t2))
        | substitute (LAMBDA (VAR z,t1),x,t2) = LAMBDA(VAR z,substitute(t1,x,t2))
        | substitute (APP (z1,z2),x,t2) = APP(substitute(z1,x,t2),substitute(z2,x,t2))

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
        | repeat (LAMBDA (VAR x,t)) = LAMBDA(VAR x,repeat t)
        | repeat (APP(LAMBDA(VAR x,t1),t2)) = repeat(substitute(t1,x,t2))
        | repeat (APP(t1,t2)) = APP(repeat t1,repeat t2)

    val (conv,mapG,mapL,count) = alphaRenaming(t,0,1,[],[])
    val reduced = if(isWellTyped conv) then repeat(conv) else raise Not_welltyped
  in
    if(reduced = t) then reduced
    else betanf reduced
  end

(* ----------------------------------------------------------------------------------------- *)

 (* datatype temp = 
    MAP of string * int

  fun findId ([],x) = ~1
        | findId (MAP(s,value)::t,x) = 
          if(s=x) then value else findId(t,x)

  fun findStr([],x) = "~1"
      | findStr (MAP(s,value)::t,x) = if(Int.toString(value) = x) then s else findStr(t,x)

  fun insertMap (l,x,v) = if(findId (l,x) = ~1) then MAP(x,v)::l else l
*)
   (* SCOPE = 0 LOCAL---------------SCOPE = 1 GLOBAL *)
(*
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
                                                                                        else alphaRenaming(x2,count+1,0,mapG,MAP(x1,count+1)::mapL)
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
*)