
(*  fun isWellTyped t = 
    let
      datatype dict = 
        PAIR of string * int 

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
(*
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
  (*                                      val (n1,L1) = checkType(x1,p3)
                                        val (n2,L2) = checkType(x2,L1)
                                        val (n3,L3) = checkType(x3,L2)
                                      in
                                        if((n1 = 0 orelse n1 = 2) andalso n2 = n3) then (n3,L3)
                                        else if((n1 = 0 orelse n1 = 2) andalso n2<> ~2 andalso n3 <> ~2) then
                                            if(n2 = 2) then (n3,L3)
                                            else (n2,L3)
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
      val (n,l) = checkType(t,[])
  in
      if(n = ~2) then false else true
  end


  local
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

  in

    fun betanf t = 
      let 
        val reduced = if(isWellTyped t) then repeat(t) else raise Not_welltyped
    in if(reduced = t) then reduced
        else betanf reduced
    end

  end
*)
(*
  
  val l1 = "LAMBDA x[(P x)]";
  val l2 = "(LAMBDA x[(S (P x))] (P z))"
  val l3 = "(ITE <LAMBDA x[(S y)],(LAMBDA y[(GTZ y)] Z),(S (P Z))>)"
  val l4 = "(ITE <LAMBDA x[(S y)],(LAMBDA y[(S y)] Z),(S (P Z))>)"
  val l5 = "(ITE <LAMBDA x[(IZ y)],(LAMBDA y[(S y)] Z),(S (P Z))>)"

  val t1 = P (ITE (LAMBDA (VAR "x",IZ (S T)),Z,Z));                                          (*false*)
  val t18 = P (APP (LAMBDA (VAR "x",ITE(T,S (VAR "x"),Z)),T));                                 (*false*) 
  val t2 = P (APP (LAMBDA (VAR "x",ITE(T,S (VAR "x"),Z)),Z)) ;                                 (*true*)
  val t3 = IZ (ITE (LAMBDA (VAR "x",IZ (VAR "x")),S (P Z),Z)) ;                               (*false*) 
  val t4 = APP (LAMBDA (VAR "y",ITE (LAMBDA (VAR "x",IZ (VAR "x")),S (P Z),Z)),T);             (*false*)
  val t5 = APP (LAMBDA (VAR "y",ITE (LAMBDA (VAR "x",IZ (VAR "x")),S (P (VAR "y")),Z)),T);    (*false*) 
  val t6 = LAMBDA (VAR "x",ITE(IZ (P(S (VAR "x"))),IZ Z,T));                                   (*true*)
  val t7 = APP(LAMBDA (VAR "x",ITE(IZ (P(S (VAR "x"))),IZ Z,T)),IZ Z);                         (*false*)
  val t8 = APP(LAMBDA (VAR "x",ITE(IZ (P(S (VAR "x"))),IZ Z,T)),P (S Z));                      (*true*)
  val t9 = APP(LAMBDA (VAR "x",ITE(IZ (P(S (VAR "x"))),IZ Z,T)),ITE(T,P (S Z),T));             (*false*)
  val t10 = APP(LAMBDA (VAR "x",ITE(VAR "x",IZ Z,T)),ITE(T,P (S Z),T));                        (*false*)
  val t11 = APP(APP(LAMBDA(VAR "x",LAMBDA(VAR "y",ITE(T,VAR "x",VAR "y"))),T),Z);              (*FALSE*)
  val t12 = APP(LAMBDA(VAR "x",LAMBDA(VAR "y",ITE(T,VAR "x",VAR "y"))),T);                     (*true*)
  val t13 = APP(VAR "y",VAR "y");                                                              (*false*)
  val t14 = APP(LAMBDA(VAR "x",ITE(T,VAR "y",F)),ITE(T,VAR "y",Z));                            (*false*)
  val t15 = APP(LAMBDA(VAR "x",ITE(VAR "y",VAR "y",VAR "x")),T);                               (*true*)
  val t16 = APP(LAMBDA(VAR "x",ITE(VAR "y",VAR "y",VAR "x")),Z);                               (*false*)
 
  val t17 = APP(LAMBDA(VAR "x",LAMBDA(VAR "y",APP(VAR "y",VAR "y"))),LAMBDA(VAR "x",LAMBDA(VAR "y",APP(VAR "x",VAR "y")))); (*false*)
  
  val t19 = APP(APP(LAMBDA(VAR "x",LAMBDA(VAR "y",ITE(F,VAR "y",VAR "x"))),VAR "y"),VAR "z")  ; (*true*)

  val t20 = APP
    (APP
       (LAMBDA (VAR "x",LAMBDA (VAR "y",APP (VAR "x",VAR "y"))),
        LAMBDA (VAR "x",VAR "x")),LAMBDA (VAR "x",Z)) ;                                       (*true*)

  val t21 = APP
       (LAMBDA (VAR "x",LAMBDA (VAR "y",APP (VAR "x",VAR "y"))),
        LAMBDA (VAR "x",VAR "x"))                                                               (*true*)

  val n1 = ITE(VAR "x",VAR "y",VAR "y");                                                          (* true *)
  val n2 = ITE(VAR "x",VAR "y",VAR "z");                                                          (* true *)
  val n3 = ITE(VAR "x",ITE(T,VAR "x",F),VAR "z");                                                 (* true *)
  val n4 = ITE(VAR "x",VAR "y",ITE(T,VAR "z",F));                                                 (* true *)
  val n5 = ITE(VAR "x",VAR "y",ITE(T,VAR "z",GTZ (S (VAR "z"))));                                 (* false *)
  val n6 = ITE(VAR "x",VAR "y",ITE(T,VAR "z",GTZ (S (VAR "p"))));                                 (* true *)
  val n7 = ITE(VAR "x",IZ (VAR "y"),ITE(T,VAR "z",GTZ(S (VAR "p"))));                             (* true *)
  val n8 = ITE(VAR "x",APP(LAMBDA (VAR "y",LAMBDA(VAR "x",GTZ(S (P (S (S (VAR "y"))))))),F),F);   (* false *)

  ALPHA CONVERSION

  alphaConversion (LAMBDA (VAR "x",ITE(VAR "x",ITE(VAR "x",VAR "y",VAR "y"),VAR "z")),0,[],[]);
  alphaConversion (LAMBDA (VAR "x",ITE(VAR "x",ITE(VAR "x",VAR "y",VAR "z"),VAR "z")),0,[],[]);
  alphaConversion (LAMBDA (VAR "x",ITE(VAR "x",VAR "y",VAR "z")),0,[],[]);
  alphaConversion (LAMBDA (VAR "x",ITE(VAR "x",LAMBDA(VAR "y",ITE(VAR "x",VAR "y",S (VAR "z"))),VAR "y")),0,[],[])
  APP (LAMBDA(VAR "x",ITE(VAR "x",LAMBDA(VAR "y",ITE(VAR "x",VAR "y",S (VAR "z"))),VAR "y")),VAR "y")
  APP(APP(LAMBDA(VAR "x",(ITE(VAR "x",VAR "y",VAR "y"))),VAR "x"),VAR "x")
  APP(LAMBDA(VAR "x",S (VAR "x")),ITE (LAMBDA(VAR "x",LAMBDA (VAR "y",VAR "z")),LAMBDA(VAR "y",VAR "x"),Z))

*)

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



(*--------------------------------------------------------------------------------------------------------*)

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









| checkType (ITE(x1,x2,x3),l) = let
                                            val p1 = if(checkVar(x1) <> "" andalso find(l,checkVar(x1)) = ~1) then 
                                                        insert(l,checkVar x1,0) 
                                                      else l
                                            val p2 = if(checkVar(x2) <> "" andalso find(p1,checkVar(x1)) = ~1) then 
                                                        insert(p1,checkVar x2,3) 
                                                      else p1
                                            val p3 = if(checkVar(x3) <> "" andalso find(p2,checkVar(x1)) = ~1) then 
                                                        insert(p2,checkVar x3,3) 
                                                      else p2
                                            val (typ1,i11,i12,L1) = checkType(x1,p3)
                                            val (typ2,i21,i22,L2) = checkType(x2,L1)
                                            val (typ3,i31,i32,L3) = checkType(x3,L2)
                                          in
                                            if(typ1 = 0) then
                                              if(typ2 = 2 andalso typ3 <> 2) then (~2,~1,~1,L3)
                                              else if (typ2 <> 2 andalso typ3 = 2) then (~2,~1,~1,L3)
                                              if(typ2 <> 2 andalso typ3 <> 2) then 
                                                if(typ2 = typ3) then (typ2,~1,~1,L3)
                                                else if(typ2 = 3 andalso checkVar(x2) <> "") then (typ3,~1,~1,update(L3,x2,typ3,[]))
                                                else if(typ2 = 3 andalso checkVar(x2) = "") then (~2,~1,~1,L3)
                                                else if(typ3 = 3 andalso checkVar(x3) <> "") then (typ2,~1,~1,update(L3,x3,typ2,[]))
                                                else (~2,~1,~1,L3)
                                              else functionCheck(i21,i31,i22,i32,L3)

                                              if(typ2 = typ3 andalso i21 = i31 andalso i22 = i32) then (typ2,i21,i22,L3)
                                              else if(typ2 = 3 )
                                            else if(typ1 = 3) then

                                            else (~2,~1,~1,L3)
                                          end



      fun checkType (Z,l) = (1,~1,~1,l)
          | checkType (T,l) = (0,~1,~1,l)
          | checkType (F,l) = (0,~1,~1,l)
          | checkType (VAR x,l) = if(find(l,x) = ~1) then (3,~1,~1,insert(l,x,3))
                                  else (find(l,x),~1,~1,l)
          | checkType (P (VAR x),l) = if(find(l,x) = ~1) then (1,~1,~1,insert(l,x,1))
                                      else if(find(l,x) = 1) then (1,~1,~1,l)
                                      else if(find(l,x) = 3) then (1,~1,~1,update(l,x,1,[]))
                                      else (~2,~1,~1,l)
          | checkType (P x,l) = let
                                  val (typ,i1,i2,L) = checkType (x,l)
                                in
                                  if(typ = 1 orelse typ = 3) then (1,~1,~1,L) else (~2,~1,~1,L)
                                end
          | checkType (S (VAR x),l) = if(find(l,x) = ~1) then (1,~1,~1,insert(l,x,1))
                                      else if(find(l,x) = 1) then (1,~1,~1,l)
                                      else if(find(l,x) = 3) then (1,~1,~1,update(l,x,1,[]))
                                      else (~2,~1,~1,l)
          | checkType (S x,l) = let
                                  val (typ,i1,i2,L) = checkType (x,l)
                                in
                                  if(typ = 1 orelse typ = 3) then (1,~1,~1,L) else (~2,~1,~1,L)
                                end
          | checkType (IZ (VAR x),l) = if(find(l,x) = ~1) then (0,~1,~1,insert(l,x,1))
                                      else if(find(l,x) = 1) then (0,~1,~1,l)
                                      else if(find(l,x) = 3) then (0,~1,~1,update(l,x,1,[]))
                                      else (~2,~1,~1,l) 
          | checkType (IZ x,l) = let
                                  val (typ,i1,i2,L) = checkType (x,l)
                                in
                                  if(typ = 1 orelse typ = 3) then (0,~1,~1,L) else (~2,~1,~1,L)
                                end
          | checkType (GTZ (VAR x),l) = if(find(l,x) = ~1) then (0,~1,~1,insert(l,x,1))
                                      else if(find(l,x) = 1) then (0,~1,~1,l)
                                      else if(find(l,x) = 3) then (0,~1,~1,update(l,x,1,[]))
                                      else (~2,~1,~1,l) 
          | checkType (GTZ x,l) = let
                                    val (typ,i1,i2,L) = checkType (x,l)
                                  in
                                    if(typ = 1 orelse typ = 3) then (0,~1,~1,L) else (~2,~1,~1,L)
                                  end
          | checkType (ITE (x1,x2,x3),l) = let
                                              val p1 = if(checkVar(x1) <> "" andalso find(l,checkVar(x1)) = ~1) then 
                                                        insert(l,checkVar x1,0) 
                                                      else l
                                              val p2 = if(checkVar(x2) <> "" andalso find(p1,checkVar(x1)) = ~1) then 
                                                        insert(p1,checkVar x2,3) 
                                                      else p1
                                              val p3 = if(checkVar(x3) <> "" andalso find(p2,checkVar(x1)) = ~1) then 
                                                        insert(p2,checkVar x3,3) 
                                                      else p2
                                              val (typ1,i11,i12,L1) = checkType (x1,p3)
                                              val (typ2,i21,i22,L2) = checkType (x2,L1)
                                              val (typ3,i31,i32,L3) = checkType (x3,L2)
                                            in
                                              if(typ1 = 0 orelse typ1 = 3) then
                                                if(typ2 = 2 orelse typ3 = 2) then (~2,~1,~1,L3) 
                                                else if(typ2 = typ3) then (typ2,~1,~1,L3)
                                                else if(typ2 = 3) then
                                                  if(checkVar(x2) <> "") then (typ3,~1,~1,update(L3,checkVar(x2),typ3,[]))
                                                  else (typ3,~1,~1,L3)
                                                else if(checkVar(x3) <> "") then (typ2,~1,~1,update(L3,checkVar(x3),typ2,[]))
                                                else (typ2,~1,~1,L3)
                                              else (~2,~1,~1,L3) 
                                            end
          | checkType (LAMBDA (VAR x1,x2),l) = let
                                                val (typ,i1,i2,L) = if(find(l,x1) = ~1) then checkType (x2,insert(l,x1,3))  
                                                                    else checkType (x2,l)
                                              in
                                                if(typ = 2) then (2,find(L,x1),i2,L)
                                                else (2,find(L,x1),typ,L)
                                              end
          | checkType (APP (LAMBDA (VAR x1,x2),x3),l) = let
                                                      val (typ2,i21,i22,L2) = checkType (x3,l)
                                                      val (typ1,i11,i12,L1) = if(find(l,x1) = ~1)
                                                                                if(typ2 <> 2) then
                                                                                  checkType (x2,insert(L2,x1,typ2))
                                                                                else checkType (x2,insert(L2,x1,i22))
                                                                              else checkType(x2,L2)
                                                    in
                                                      (typ1,i11,i12,L1)
                                                    end
          | checkType (APP(APP(x1,x2),x3),l) = let
                                          val (typ1,i11,i12,L1) = checkType (APP(x1,x2),l)
                                          val (typ2,i21,i22,L2) = checkType (x3,L1)
                                          reduce(x1,x2,l)
                                        in
                                          if(typ1 <> 2) then (~2,~1,~1,L2)
                                          else if(typ2 = 2) then
                                            if(i11 = i21) then ()
                                            else if(i11 = 3) then
                                            else  
                                          else  
                                        end
          | checkType (APP(_,_),l) = (~2,~1,~1,l)
          | checkType (LAMBDA(_,_),l) = (~2,~1,~1,l)




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