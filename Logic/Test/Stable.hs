module Logic.Test.Stable where

result10 :: String
result10 = unlines
    [ "(set-option :auto-config false)"
    , "(set-option :smt.timeout 3000)"
    , "(declare-datatypes (a) ( (Maybe (Just (fromJust a)) Nothing) ))"
    , "(declare-datatypes () ( (Null null) ))"
    , "(declare-datatypes (a b) ( (Pair (pair (first a) (second b))) ))"
    , "(declare-datatypes (a1 a2)"
    , "                   ( (Record-b-x (Record-b-x (@@field@@_b a1) (@@field@@_x a2))) ))"
    , "; comment: we don't need to declare the sort Bool"
    , "; comment: we don't need to declare the sort Int"
    , "; comment: we don't need to declare the sort Real"
    , "(define-sort set (a) (Array a Bool))"
    , "(declare-const v1 (Record-b-x Bool Int))"
    , "(declare-const v2 (Record-b-x Bool Int))"
    , "; v1: x:=7, b:=true"
    , "(assert (= v1 (Record-b-x true 7)))"
    , "; v2: v1[x:=7]"
    , "(assert (= v2 (Record-b-x (@@field@@_b v1) 7)))"
    , "(assert (not (= v1 v2)))"
    , "(check-sat-using (or-else (then qe smt)"
    , "                          (then simplify smt)"
    , "                          (then skip smt)"
    , "                          (then (using-params simplify :expand-power true) smt)))"
    ]

result11 :: String
result11 = unlines
    [ "(set-option :auto-config false)"
    , "(set-option :smt.timeout 3000)"
    , "(declare-datatypes (a) ( (Maybe (Just (fromJust a)) Nothing) ))"
    , "(declare-datatypes () ( (Null null) ))"
    , "(declare-datatypes (a b) ( (Pair (pair (first a) (second b))) ))"
    , "(declare-datatypes (a1 a2)"
    , "                   ( (Record-b-x (Record-b-x (@@field@@_b a1) (@@field@@_x a2))) ))"
    , "; comment: we don't need to declare the sort Bool"
    , "; comment: we don't need to declare the sort Int"
    , "; comment: we don't need to declare the sort Real"
    , "(define-sort set (a) (Array a Bool))"
    , "(declare-const v1 (Record-b-x Bool Int))"
    , "(declare-const v2 (Record-b-x Bool Int))"
    , "(declare-fun card@@Bool ( (set Bool) ) Int)"
    , "(declare-fun card@@Int ( (set Int) ) Int)"
    , "(declare-fun card@Open@@Record-b-x@@Bool@@Int@Close"
    , "             ( (set (Record-b-x Bool Int)) )"
    , "             Int)"
    , "(declare-fun const@Open@@Record-b-x@@Bool@@Int@Close@Open@@Record-b-x@@Bool@@Int@Close"
    , "             ( (Record-b-x Bool Int) )"
    , "             (Array (Record-b-x Bool Int) (Record-b-x Bool Int)))"
    , "(declare-fun finite@@Bool ( (set Bool) ) Bool)"
    , "(declare-fun finite@@Int ( (set Int) ) Bool)"
    , "(declare-fun finite@Open@@Record-b-x@@Bool@@Int@Close"
    , "             ( (set (Record-b-x Bool Int)) )"
    , "             Bool)"
    , "(declare-fun ident@Open@@Record-b-x@@Bool@@Int@Close"
    , "             ()"
    , "             (Array (Record-b-x Bool Int) (Record-b-x Bool Int)))"
    , "(declare-fun mk-set@@Bool (Bool) (set Bool))"
    , "(declare-fun mk-set@@Int (Int) (set Int))"
    , "(declare-fun mk-set@Open@@Record-b-x@@Bool@@Int@Close"
    , "             ( (Record-b-x Bool Int) )"
    , "             (set (Record-b-x Bool Int)))"
    , "(declare-fun set@Open@@Record-b-x@@Bool@@Int@Close@Open@@Record-b-x@@Bool@@Int@Close"
    , "             ( (set (Record-b-x Bool Int))"
    , "               (Array (Record-b-x Bool Int) (Record-b-x Bool Int)) )"
    , "             (set (Record-b-x Bool Int)))"
    , "(declare-fun @@lambda@@_0"
    , "             ( (set Bool)"
    , "               (set Int) )"
    , "             (set (Record-b-x Bool Int)))"
    , "(define-fun all@@Bool"
    , "            ()"
    , "            (set Bool)"
    , "            ( (as const (set Bool))"
    , "              true ))"
    , "(define-fun all@@Int () (set Int) ( (as const (set Int)) true ))"
    , "(define-fun all@Open@@Record-b-x@@Bool@@Int@Close"
    , "            ()"
    , "            (set (Record-b-x Bool Int))"
    , "            ( (as const (set (Record-b-x Bool Int)))"
    , "              true ))"
    , "(define-fun compl@@Bool"
    , "            ( (s1 (set Bool)) )"
    , "            (set Bool)"
    , "            ( (_ map not)"
    , "              s1 ))"
    , "(define-fun compl@@Int"
    , "            ( (s1 (set Int)) )"
    , "            (set Int)"
    , "            ( (_ map not)"
    , "              s1 ))"
    , "(define-fun compl@Open@@Record-b-x@@Bool@@Int@Close"
    , "            ( (s1 (set (Record-b-x Bool Int))) )"
    , "            (set (Record-b-x Bool Int))"
    , "            ( (_ map not)"
    , "              s1 ))"
    , "(define-fun elem@@Bool"
    , "            ( (x Bool)"
    , "              (s1 (set Bool)) )"
    , "            Bool"
    , "            (select s1 x))"
    , "(define-fun elem@@Int"
    , "            ( (x Int)"
    , "              (s1 (set Int)) )"
    , "            Bool"
    , "            (select s1 x))"
    , "(define-fun elem@Open@@Record-b-x@@Bool@@Int@Close"
    , "            ( (x (Record-b-x Bool Int))"
    , "              (s1 (set (Record-b-x Bool Int))) )"
    , "            Bool"
    , "            (select s1 x))"
    , "(define-fun empty-set@@Bool"
    , "            ()"
    , "            (set Bool)"
    , "            ( (as const (set Bool))"
    , "              false ))"
    , "(define-fun empty-set@@Int"
    , "            ()"
    , "            (set Int)"
    , "            ( (as const (set Int))"
    , "              false ))"
    , "(define-fun empty-set@Open@@Record-b-x@@Bool@@Int@Close"
    , "            ()"
    , "            (set (Record-b-x Bool Int))"
    , "            ( (as const (set (Record-b-x Bool Int)))"
    , "              false ))"
    , "(define-fun set-diff@@Bool"
    , "            ( (s1 (set Bool))"
    , "              (s2 (set Bool)) )"
    , "            (set Bool)"
    , "            (intersect s1 ( (_ map not) s2 )))"
    , "(define-fun set-diff@@Int"
    , "            ( (s1 (set Int))"
    , "              (s2 (set Int)) )"
    , "            (set Int)"
    , "            (intersect s1 ( (_ map not) s2 )))"
    , "(define-fun set-diff@Open@@Record-b-x@@Bool@@Int@Close"
    , "            ( (s1 (set (Record-b-x Bool Int)))"
    , "              (s2 (set (Record-b-x Bool Int))) )"
    , "            (set (Record-b-x Bool Int))"
    , "            (intersect s1 ( (_ map not) s2 )))"
    , "(define-fun st-subset@@Bool"
    , "            ( (s1 (set Bool))"
    , "              (s2 (set Bool)) )"
    , "            Bool"
    , "            (and (subset s1 s2) (not (= s1 s2))))"
    , "(define-fun st-subset@@Int"
    , "            ( (s1 (set Int))"
    , "              (s2 (set Int)) )"
    , "            Bool"
    , "            (and (subset s1 s2) (not (= s1 s2))))"
    , "(define-fun st-subset@Open@@Record-b-x@@Bool@@Int@Close"
    , "            ( (s1 (set (Record-b-x Bool Int)))"
    , "              (s2 (set (Record-b-x Bool Int))) )"
    , "            Bool"
    , "            (and (subset s1 s2) (not (= s1 s2))))"
    , "(assert (forall ( (r (set Bool)) )"
    , "                (! (=> (finite@@Bool r) (<= 0 (card@@Bool r)))"
    , "                   :pattern"
    , "                   ( (<= 0 (card@@Bool r)) ))))"
    , "(assert (forall ( (r (set Int)) )"
    , "                (! (=> (finite@@Int r) (<= 0 (card@@Int r)))"
    , "                   :pattern"
    , "                   ( (<= 0 (card@@Int r)) ))))"
    , "(assert (forall ( (r (set (Record-b-x Bool Int))) )"
    , "                (! (=> (finite@Open@@Record-b-x@@Bool@@Int@Close r)"
    , "                       (<= 0 (card@Open@@Record-b-x@@Bool@@Int@Close r)))"
    , "                   :pattern"
    , "                   ( (<= 0 (card@Open@@Record-b-x@@Bool@@Int@Close r)) ))))"
    , "(assert (forall ( (r (set Bool)) )"
    , "                (! (= (= (card@@Bool r) 0) (= r empty-set@@Bool))"
    , "                   :pattern"
    , "                   ( (card@@Bool r) ))))"
    , "(assert (forall ( (r (set Int)) )"
    , "                (! (= (= (card@@Int r) 0) (= r empty-set@@Int))"
    , "                   :pattern"
    , "                   ( (card@@Int r) ))))"
    , "(assert (forall ( (r (set (Record-b-x Bool Int))) )"
    , "                (! (= (= (card@Open@@Record-b-x@@Bool@@Int@Close r) 0)"
    , "                      (= r empty-set@Open@@Record-b-x@@Bool@@Int@Close))"
    , "                   :pattern"
    , "                   ( (card@Open@@Record-b-x@@Bool@@Int@Close r) ))))"
    , "(assert (forall ( (x Bool) )"
    , "                (! (= (card@@Bool (mk-set@@Bool x)) 1)"
    , "                   :pattern"
    , "                   ( (card@@Bool (mk-set@@Bool x)) ))))"
    , "(assert (forall ( (x Int) )"
    , "                (! (= (card@@Int (mk-set@@Int x)) 1)"
    , "                   :pattern"
    , "                   ( (card@@Int (mk-set@@Int x)) ))))"
    , "(assert (forall ( (x (Record-b-x Bool Int)) )"
    , "                (! (= (card@Open@@Record-b-x@@Bool@@Int@Close (mk-set@Open@@Record-b-x@@Bool@@Int@Close x))"
    , "                      1)"
    , "                   :pattern"
    , "                   ( (card@Open@@Record-b-x@@Bool@@Int@Close (mk-set@Open@@Record-b-x@@Bool@@Int@Close x)) ))))"
    , "(assert (forall ( (r (set Bool)) )"
    , "                (! (= (= (card@@Bool r) 1)"
    , "                      (exists ( (x Bool) ) (and true (= r (mk-set@@Bool x)))))"
    , "                   :pattern"
    , "                   ( (card@@Bool r) ))))"
    , "(assert (forall ( (r (set Int)) )"
    , "                (! (= (= (card@@Int r) 1)"
    , "                      (exists ( (x Int) ) (and true (= r (mk-set@@Int x)))))"
    , "                   :pattern"
    , "                   ( (card@@Int r) ))))"
    , "(assert (forall ( (r (set (Record-b-x Bool Int))) )"
    , "                (! (= (= (card@Open@@Record-b-x@@Bool@@Int@Close r) 1)"
    , "                      (exists ( (x (Record-b-x Bool Int)) )"
    , "                              (and true"
    , "                                   (= r (mk-set@Open@@Record-b-x@@Bool@@Int@Close x)))))"
    , "                   :pattern"
    , "                   ( (card@Open@@Record-b-x@@Bool@@Int@Close r) ))))"
    , "(assert (forall ( (r (set Bool))"
    , "                  (r0 (set Bool)) )"
    , "                (! (=> (= (intersect r r0) empty-set@@Bool)"
    , "                       (= (card@@Bool (union r r0))"
    , "                          (+ (card@@Bool r) (card@@Bool r0))))"
    , "                   :pattern"
    , "                   ( (card@@Bool (union r r0)) ))))"
    , "(assert (forall ( (r (set Int))"
    , "                  (r0 (set Int)) )"
    , "                (! (=> (= (intersect r r0) empty-set@@Int)"
    , "                       (= (card@@Int (union r r0))"
    , "                          (+ (card@@Int r) (card@@Int r0))))"
    , "                   :pattern"
    , "                   ( (card@@Int (union r r0)) ))))"
    , "(assert (forall ( (r (set (Record-b-x Bool Int)))"
    , "                  (r0 (set (Record-b-x Bool Int))) )"
    , "                (! (=> (= (intersect r r0)"
    , "                          empty-set@Open@@Record-b-x@@Bool@@Int@Close)"
    , "                       (= (card@Open@@Record-b-x@@Bool@@Int@Close (union r r0))"
    , "                          (+ (card@Open@@Record-b-x@@Bool@@Int@Close r)"
    , "                             (card@Open@@Record-b-x@@Bool@@Int@Close r0))))"
    , "                   :pattern"
    , "                   ( (card@Open@@Record-b-x@@Bool@@Int@Close (union r r0)) ))))"
    , "(assert (forall ( (x Bool)"
    , "                  (y Bool) )"
    , "                (! (= (elem@@Bool x (mk-set@@Bool y)) (= x y))"
    , "                   :pattern"
    , "                   ( (elem@@Bool x (mk-set@@Bool y)) ))))"
    , "(assert (forall ( (x Int)"
    , "                  (y Int) )"
    , "                (! (= (elem@@Int x (mk-set@@Int y)) (= x y))"
    , "                   :pattern"
    , "                   ( (elem@@Int x (mk-set@@Int y)) ))))"
    , "(assert (forall ( (x (Record-b-x Bool Int))"
    , "                  (y (Record-b-x Bool Int)) )"
    , "                (! (= (elem@Open@@Record-b-x@@Bool@@Int@Close x (mk-set@Open@@Record-b-x@@Bool@@Int@Close y))"
    , "                      (= x y))"
    , "                   :pattern"
    , "                   ( (elem@Open@@Record-b-x@@Bool@@Int@Close x (mk-set@Open@@Record-b-x@@Bool@@Int@Close y)) ))))"
    , "(assert (forall ( (r1 (set (Record-b-x Bool Int)))"
    , "                  (term (Array (Record-b-x Bool Int) (Record-b-x Bool Int)))"
    , "                  (y (Record-b-x Bool Int)) )"
    , "                (! (= (elem@Open@@Record-b-x@@Bool@@Int@Close y"
    , "                                                              (set@Open@@Record-b-x@@Bool@@Int@Close@Open@@Record-b-x@@Bool@@Int@Close r1 term))"
    , "                      (exists ( (x (Record-b-x Bool Int)) )"
    , "                              (and (elem@Open@@Record-b-x@@Bool@@Int@Close x r1)"
    , "                                   (= (select term x) y))))"
    , "                   :pattern"
    , "                   ( (elem@Open@@Record-b-x@@Bool@@Int@Close y"
    , "                                                             (set@Open@@Record-b-x@@Bool@@Int@Close@Open@@Record-b-x@@Bool@@Int@Close r1 term)) ))))"
    , "(assert (forall ( (r1 (set (Record-b-x Bool Int)))"
    , "                  (term (Array (Record-b-x Bool Int) (Record-b-x Bool Int)))"
    , "                  (y (Record-b-x Bool Int)) )"
    , "                (! (= (= (set@Open@@Record-b-x@@Bool@@Int@Close@Open@@Record-b-x@@Bool@@Int@Close r1 term)"
    , "                         (mk-set@Open@@Record-b-x@@Bool@@Int@Close y))"
    , "                      (forall ( (x (Record-b-x Bool Int)) )"
    , "                              (=> (elem@Open@@Record-b-x@@Bool@@Int@Close x r1)"
    , "                                  (= (select term x) y))))"
    , "                   :pattern"
    , "                   ( (set@Open@@Record-b-x@@Bool@@Int@Close@Open@@Record-b-x@@Bool@@Int@Close r1 term)"
    , "                     (mk-set@Open@@Record-b-x@@Bool@@Int@Close y) ))))"
    , "(assert (forall ( (s1 (set Bool))"
    , "                  (s2 (set Bool)) )"
    , "                (! (=> (finite@@Bool s1)"
    , "                       (finite@@Bool (set-diff@@Bool s1 s2)))"
    , "                   :pattern"
    , "                   ( (finite@@Bool (set-diff@@Bool s1 s2)) ))))"
    , "(assert (forall ( (s1 (set Int))"
    , "                  (s2 (set Int)) )"
    , "                (! (=> (finite@@Int s1)"
    , "                       (finite@@Int (set-diff@@Int s1 s2)))"
    , "                   :pattern"
    , "                   ( (finite@@Int (set-diff@@Int s1 s2)) ))))"
    , "(assert (forall ( (s1 (set (Record-b-x Bool Int)))"
    , "                  (s2 (set (Record-b-x Bool Int))) )"
    , "                (! (=> (finite@Open@@Record-b-x@@Bool@@Int@Close s1)"
    , "                       (finite@Open@@Record-b-x@@Bool@@Int@Close (set-diff@Open@@Record-b-x@@Bool@@Int@Close s1 s2)))"
    , "                   :pattern"
    , "                   ( (finite@Open@@Record-b-x@@Bool@@Int@Close (set-diff@Open@@Record-b-x@@Bool@@Int@Close s1 s2)) ))))"
    , "(assert (forall ( (s1 (set Bool))"
    , "                  (s2 (set Bool)) )"
    , "                (! (=> (and (finite@@Bool s1) (finite@@Bool s2))"
    , "                       (finite@@Bool (union s1 s2)))"
    , "                   :pattern"
    , "                   ( (finite@@Bool (union s1 s2)) ))))"
    , "(assert (forall ( (s1 (set Int))"
    , "                  (s2 (set Int)) )"
    , "                (! (=> (and (finite@@Int s1) (finite@@Int s2))"
    , "                       (finite@@Int (union s1 s2)))"
    , "                   :pattern"
    , "                   ( (finite@@Int (union s1 s2)) ))))"
    , "(assert (forall ( (s1 (set (Record-b-x Bool Int)))"
    , "                  (s2 (set (Record-b-x Bool Int))) )"
    , "                (! (=> (and (finite@Open@@Record-b-x@@Bool@@Int@Close s1)"
    , "                            (finite@Open@@Record-b-x@@Bool@@Int@Close s2))"
    , "                       (finite@Open@@Record-b-x@@Bool@@Int@Close (union s1 s2)))"
    , "                   :pattern"
    , "                   ( (finite@Open@@Record-b-x@@Bool@@Int@Close (union s1 s2)) ))))"
    , "(assert (forall ( (s1 (set Bool))"
    , "                  (s2 (set Bool)) )"
    , "                (! (=> (and (finite@@Bool s2) (not (finite@@Bool s1)))"
    , "                       (not (finite@@Bool (set-diff@@Bool s1 s2))))"
    , "                   :pattern"
    , "                   ( (finite@@Bool (set-diff@@Bool s1 s2)) ))))"
    , "(assert (forall ( (s1 (set Int))"
    , "                  (s2 (set Int)) )"
    , "                (! (=> (and (finite@@Int s2) (not (finite@@Int s1)))"
    , "                       (not (finite@@Int (set-diff@@Int s1 s2))))"
    , "                   :pattern"
    , "                   ( (finite@@Int (set-diff@@Int s1 s2)) ))))"
    , "(assert (forall ( (s1 (set (Record-b-x Bool Int)))"
    , "                  (s2 (set (Record-b-x Bool Int))) )"
    , "                (! (=> (and (finite@Open@@Record-b-x@@Bool@@Int@Close s2)"
    , "                            (not (finite@Open@@Record-b-x@@Bool@@Int@Close s1)))"
    , "                       (not (finite@Open@@Record-b-x@@Bool@@Int@Close (set-diff@Open@@Record-b-x@@Bool@@Int@Close s1 s2))))"
    , "                   :pattern"
    , "                   ( (finite@Open@@Record-b-x@@Bool@@Int@Close (set-diff@Open@@Record-b-x@@Bool@@Int@Close s1 s2)) ))))"
    , "(assert (forall ( (x Bool) )"
    , "                (! (finite@@Bool (mk-set@@Bool x))"
    , "                   :pattern"
    , "                   ( (finite@@Bool (mk-set@@Bool x)) ))))"
    , "(assert (forall ( (x Int) )"
    , "                (! (finite@@Int (mk-set@@Int x))"
    , "                   :pattern"
    , "                   ( (finite@@Int (mk-set@@Int x)) ))))"
    , "(assert (forall ( (x (Record-b-x Bool Int)) )"
    , "                (! (finite@Open@@Record-b-x@@Bool@@Int@Close (mk-set@Open@@Record-b-x@@Bool@@Int@Close x))"
    , "                   :pattern"
    , "                   ( (finite@Open@@Record-b-x@@Bool@@Int@Close (mk-set@Open@@Record-b-x@@Bool@@Int@Close x)) ))))"
    , "(assert (finite@@Bool empty-set@@Bool))"
    , "(assert (finite@@Int empty-set@@Int))"
    , "(assert (finite@Open@@Record-b-x@@Bool@@Int@Close empty-set@Open@@Record-b-x@@Bool@@Int@Close))"
    , "(assert (forall ( (r1 (set (Record-b-x Bool Int))) )"
    , "                (! (= (set@Open@@Record-b-x@@Bool@@Int@Close@Open@@Record-b-x@@Bool@@Int@Close r1 ident@Open@@Record-b-x@@Bool@@Int@Close)"
    , "                      r1)"
    , "                   :pattern"
    , "                   ( (set@Open@@Record-b-x@@Bool@@Int@Close@Open@@Record-b-x@@Bool@@Int@Close r1 ident@Open@@Record-b-x@@Bool@@Int@Close) ))))"
    , "(assert (forall ( (x (Record-b-x Bool Int))"
    , "                  (y (Record-b-x Bool Int)) )"
    , "                (! (= (select (const@Open@@Record-b-x@@Bool@@Int@Close@Open@@Record-b-x@@Bool@@Int@Close x)"
    , "                              y)"
    , "                      x)"
    , "                   :pattern"
    , "                   ( (select (const@Open@@Record-b-x@@Bool@@Int@Close@Open@@Record-b-x@@Bool@@Int@Close x)"
    , "                             y) ))))"
    , "(assert (forall ( (x (Record-b-x Bool Int)) )"
    , "                (! (= (select ident@Open@@Record-b-x@@Bool@@Int@Close x)"
    , "                      x)"
    , "                   :pattern"
    , "                   ( (select ident@Open@@Record-b-x@@Bool@@Int@Close x) ))))"
    , "(assert (forall ( (x Bool)"
    , "                  (y Bool) )"
    , "                (! (= (elem@@Bool x (mk-set@@Bool y)) (= x y))"
    , "                   :pattern"
    , "                   ( (elem@@Bool x (mk-set@@Bool y)) ))))"
    , "(assert (forall ( (x Int)"
    , "                  (y Int) )"
    , "                (! (= (elem@@Int x (mk-set@@Int y)) (= x y))"
    , "                   :pattern"
    , "                   ( (elem@@Int x (mk-set@@Int y)) ))))"
    , "(assert (forall ( (x (Record-b-x Bool Int))"
    , "                  (y (Record-b-x Bool Int)) )"
    , "                (! (= (elem@Open@@Record-b-x@@Bool@@Int@Close x (mk-set@Open@@Record-b-x@@Bool@@Int@Close y))"
    , "                      (= x y))"
    , "                   :pattern"
    , "                   ( (elem@Open@@Record-b-x@@Bool@@Int@Close x (mk-set@Open@@Record-b-x@@Bool@@Int@Close y)) ))))"
    , "(assert (forall ( (r1 (set (Record-b-x Bool Int)))"
    , "                  (term (Array (Record-b-x Bool Int) (Record-b-x Bool Int)))"
    , "                  (y (Record-b-x Bool Int)) )"
    , "                (! (= (elem@Open@@Record-b-x@@Bool@@Int@Close y"
    , "                                                              (set@Open@@Record-b-x@@Bool@@Int@Close@Open@@Record-b-x@@Bool@@Int@Close r1 term))"
    , "                      (exists ( (x (Record-b-x Bool Int)) )"
    , "                              (and (elem@Open@@Record-b-x@@Bool@@Int@Close x r1)"
    , "                                   (= (select term x) y))))"
    , "                   :pattern"
    , "                   ( (elem@Open@@Record-b-x@@Bool@@Int@Close y"
    , "                                                             (set@Open@@Record-b-x@@Bool@@Int@Close@Open@@Record-b-x@@Bool@@Int@Close r1 term)) ))))"
    , "(assert (forall ( (r1 (set (Record-b-x Bool Int)))"
    , "                  (term (Array (Record-b-x Bool Int) (Record-b-x Bool Int)))"
    , "                  (y (Record-b-x Bool Int)) )"
    , "                (! (= (= (set@Open@@Record-b-x@@Bool@@Int@Close@Open@@Record-b-x@@Bool@@Int@Close r1 term)"
    , "                         (mk-set@Open@@Record-b-x@@Bool@@Int@Close y))"
    , "                      (forall ( (x (Record-b-x Bool Int)) )"
    , "                              (=> (elem@Open@@Record-b-x@@Bool@@Int@Close x r1)"
    , "                                  (= (select term x) y))))"
    , "                   :pattern"
    , "                   ( (set@Open@@Record-b-x@@Bool@@Int@Close@Open@@Record-b-x@@Bool@@Int@Close r1 term)"
    , "                     (mk-set@Open@@Record-b-x@@Bool@@Int@Close y) ))))"
    , "(assert (forall ( (s1 (set Bool))"
    , "                  (s2 (set Bool)) )"
    , "                (! (=> (finite@@Bool s1)"
    , "                       (finite@@Bool (set-diff@@Bool s1 s2)))"
    , "                   :pattern"
    , "                   ( (finite@@Bool (set-diff@@Bool s1 s2)) ))))"
    , "(assert (forall ( (s1 (set Int))"
    , "                  (s2 (set Int)) )"
    , "                (! (=> (finite@@Int s1)"
    , "                       (finite@@Int (set-diff@@Int s1 s2)))"
    , "                   :pattern"
    , "                   ( (finite@@Int (set-diff@@Int s1 s2)) ))))"
    , "(assert (forall ( (s1 (set (Record-b-x Bool Int)))"
    , "                  (s2 (set (Record-b-x Bool Int))) )"
    , "                (! (=> (finite@Open@@Record-b-x@@Bool@@Int@Close s1)"
    , "                       (finite@Open@@Record-b-x@@Bool@@Int@Close (set-diff@Open@@Record-b-x@@Bool@@Int@Close s1 s2)))"
    , "                   :pattern"
    , "                   ( (finite@Open@@Record-b-x@@Bool@@Int@Close (set-diff@Open@@Record-b-x@@Bool@@Int@Close s1 s2)) ))))"
    , "(assert (forall ( (s1 (set Bool))"
    , "                  (s2 (set Bool)) )"
    , "                (! (=> (and (finite@@Bool s1) (finite@@Bool s2))"
    , "                       (finite@@Bool (union s1 s2)))"
    , "                   :pattern"
    , "                   ( (finite@@Bool (union s1 s2)) ))))"
    , "(assert (forall ( (s1 (set Int))"
    , "                  (s2 (set Int)) )"
    , "                (! (=> (and (finite@@Int s1) (finite@@Int s2))"
    , "                       (finite@@Int (union s1 s2)))"
    , "                   :pattern"
    , "                   ( (finite@@Int (union s1 s2)) ))))"
    , "(assert (forall ( (s1 (set (Record-b-x Bool Int)))"
    , "                  (s2 (set (Record-b-x Bool Int))) )"
    , "                (! (=> (and (finite@Open@@Record-b-x@@Bool@@Int@Close s1)"
    , "                            (finite@Open@@Record-b-x@@Bool@@Int@Close s2))"
    , "                       (finite@Open@@Record-b-x@@Bool@@Int@Close (union s1 s2)))"
    , "                   :pattern"
    , "                   ( (finite@Open@@Record-b-x@@Bool@@Int@Close (union s1 s2)) ))))"
    , "(assert (forall ( (s1 (set Bool))"
    , "                  (s2 (set Bool)) )"
    , "                (! (=> (and (finite@@Bool s2) (not (finite@@Bool s1)))"
    , "                       (not (finite@@Bool (set-diff@@Bool s1 s2))))"
    , "                   :pattern"
    , "                   ( (finite@@Bool (set-diff@@Bool s1 s2)) ))))"
    , "(assert (forall ( (s1 (set Int))"
    , "                  (s2 (set Int)) )"
    , "                (! (=> (and (finite@@Int s2) (not (finite@@Int s1)))"
    , "                       (not (finite@@Int (set-diff@@Int s1 s2))))"
    , "                   :pattern"
    , "                   ( (finite@@Int (set-diff@@Int s1 s2)) ))))"
    , "(assert (forall ( (s1 (set (Record-b-x Bool Int)))"
    , "                  (s2 (set (Record-b-x Bool Int))) )"
    , "                (! (=> (and (finite@Open@@Record-b-x@@Bool@@Int@Close s2)"
    , "                            (not (finite@Open@@Record-b-x@@Bool@@Int@Close s1)))"
    , "                       (not (finite@Open@@Record-b-x@@Bool@@Int@Close (set-diff@Open@@Record-b-x@@Bool@@Int@Close s1 s2))))"
    , "                   :pattern"
    , "                   ( (finite@Open@@Record-b-x@@Bool@@Int@Close (set-diff@Open@@Record-b-x@@Bool@@Int@Close s1 s2)) ))))"
    , "(assert (forall ( (x Bool) )"
    , "                (! (finite@@Bool (mk-set@@Bool x))"
    , "                   :pattern"
    , "                   ( (finite@@Bool (mk-set@@Bool x)) ))))"
    , "(assert (forall ( (x Int) )"
    , "                (! (finite@@Int (mk-set@@Int x))"
    , "                   :pattern"
    , "                   ( (finite@@Int (mk-set@@Int x)) ))))"
    , "(assert (forall ( (x (Record-b-x Bool Int)) )"
    , "                (! (finite@Open@@Record-b-x@@Bool@@Int@Close (mk-set@Open@@Record-b-x@@Bool@@Int@Close x))"
    , "                   :pattern"
    , "                   ( (finite@Open@@Record-b-x@@Bool@@Int@Close (mk-set@Open@@Record-b-x@@Bool@@Int@Close x)) ))))"
    , "(assert (finite@@Bool empty-set@@Bool))"
    , "(assert (finite@@Int empty-set@@Int))"
    , "(assert (finite@Open@@Record-b-x@@Bool@@Int@Close empty-set@Open@@Record-b-x@@Bool@@Int@Close))"
    , "(assert (forall ( (r1 (set (Record-b-x Bool Int))) )"
    , "                (! (= (set@Open@@Record-b-x@@Bool@@Int@Close@Open@@Record-b-x@@Bool@@Int@Close r1 ident@Open@@Record-b-x@@Bool@@Int@Close)"
    , "                      r1)"
    , "                   :pattern"
    , "                   ( (set@Open@@Record-b-x@@Bool@@Int@Close@Open@@Record-b-x@@Bool@@Int@Close r1 ident@Open@@Record-b-x@@Bool@@Int@Close) ))))"
    , "(assert (forall ( (x (Record-b-x Bool Int))"
    , "                  (y (Record-b-x Bool Int)) )"
    , "                (! (= (select (const@Open@@Record-b-x@@Bool@@Int@Close@Open@@Record-b-x@@Bool@@Int@Close x)"
    , "                              y)"
    , "                      x)"
    , "                   :pattern"
    , "                   ( (select (const@Open@@Record-b-x@@Bool@@Int@Close@Open@@Record-b-x@@Bool@@Int@Close x)"
    , "                             y) ))))"
    , "(assert (forall ( (x (Record-b-x Bool Int)) )"
    , "                (! (= (select ident@Open@@Record-b-x@@Bool@@Int@Close x)"
    , "                      x)"
    , "                   :pattern"
    , "                   ( (select ident@Open@@Record-b-x@@Bool@@Int@Close x) ))))"
    , "(assert (forall ( (@@fv@@_0 (set Bool))"
    , "                  (@@fv@@_1 (set Int))"
    , "                  (@@bv@@_0 (Record-b-x Bool Int)) )"
    , "                (! (= (elem@Open@@Record-b-x@@Bool@@Int@Close @@bv@@_0 (@@lambda@@_0 @@fv@@_0 @@fv@@_1))"
    , "                      (and (elem@@Bool (@@field@@_b @@bv@@_0) @@fv@@_0)"
    , "                           (elem@@Int (@@field@@_x @@bv@@_0) @@fv@@_1)))"
    , "                   :pattern"
    , "                   ( (elem@Open@@Record-b-x@@Bool@@Int@Close @@bv@@_0 (@@lambda@@_0 @@fv@@_0 @@fv@@_1)) ))))"
    , "; expr: { v1: x:=7, b:=true }"
    , "(assert (= v1 (Record-b-x true 7)))"
    , "; expr: { v2 \\in ['x : {7}, 'b : (all:\\set[ \\Bool])] }"
    , "(assert (elem@Open@@Record-b-x@@Bool@@Int@Close v2"
    , "                                                (set@Open@@Record-b-x@@Bool@@Int@Close@Open@@Record-b-x@@Bool@@Int@Close (@@lambda@@_0 all@@Bool (mk-set@@Int 7))"
    , "                                                                                                                         ident@Open@@Record-b-x@@Bool@@Int@Close)))"
    , "(assert (not (= v1 v2)))"
    , "(check-sat-using (or-else (then qe smt)"
    , "                          (then simplify smt)"
    , "                          (then skip smt)"
    , "                          (then (using-params simplify :expand-power true) smt)))"
    ]


