(set-logic HORN)
(set-info :source |
  Benchmark: ../golem/build/RealCodeNested/originalcodeLogicOpenSMTsceletonDeep1.c
  Generated by Korn 0.4 https://github.com/gernst/korn
|)


(declare-fun $main_sum2 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun $main_if5 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun __assert_fail (Int Int Int Int) Bool)
(declare-fun $main_inv1 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun $main_if6 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun $__VERIFIER_assert_pre (Int) Bool)
(declare-fun $__VERIFIER_assert_if1 (Int Int) Bool)
(declare-fun $main_sum3 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun $main_if2 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun $main_if4 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun $main_inv5 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun $main_if3 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun $main_inv4 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun $main_if7 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun $main_inv2 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun __VERIFIER_assert (Int) Bool)
(declare-fun $main_inv3 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun $__assert_fail_pre (Int Int Int Int) Bool)
(declare-fun $main_sum5 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun $main_sum4 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun $main_sum1 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun $__VERIFIER_assert_ERROR (Int Int) Bool)

; label ERROR
(assert
  (forall ((cond!1 Int))
    (=> (and (not (not (= cond!1 0)))
             ($__VERIFIER_assert_pre cond!1))
        ($__VERIFIER_assert_ERROR cond!1 cond!1))))

; error
(assert
  (forall ((cond!1 Int) (cond!2 Int))
    (=> (and ($__VERIFIER_assert_ERROR cond!1 cond!2))
        false)))

; if else
(assert
  (forall ((cond!1 Int))
    (=> (and (not (not (not (= cond!1 0))))
             ($__VERIFIER_assert_pre cond!1))
        ($__VERIFIER_assert_if1 cond!1 cond!1))))

; post __VERIFIER_assert
(assert
  (forall ((cond!1 Int) (cond!3 Int))
    (=> (and ($__VERIFIER_assert_if1 cond!1 cond!3))
        (__VERIFIER_assert cond!1))))

; loop entry $main_inv1 (line 25)
(assert
  (forall ((hasSubstitution!20 Int) (poly!6 Int) (varToPolyIndices!9 Int) (condition!18 Int) (i!14 Int) (term!10 Int) (processedIndices!8 Int) (substitutions!4 Int) (zeroPolynomials!5 Int) (changed!15 Int) (new_keys!7 Int) (index!11 Int) (its!13 Int) (var!19 Int) (val!21 Int))
    (=> (and (<= 5 poly!6)
             (<= poly!6 100)
             (<= 10 zeroPolynomials!5)
             (<= zeroPolynomials!5 100)
             (= changed!15 0)
             (= i!14 0)
             (= its!13 0)
             (= var!19 0)
             (= index!11 0)
             (= term!10 0)
             (= varToPolyIndices!9 0)
             (= processedIndices!8 0)
             (= new_keys!7 10)
             (= substitutions!4 0))
        ($main_inv1 substitutions!4 zeroPolynomials!5 poly!6 new_keys!7 processedIndices!8 varToPolyIndices!9 term!10 index!11 var!19 its!13 i!14 changed!15 var!19 hasSubstitution!20 condition!18 var!19 hasSubstitution!20 val!21))))

; loop term $main_sum1 (line 25)
(assert
  (forall ((var!37 Int) (varToPolyIndices!27 Int) (zeroPolynomials!23 Int) (new_keys!25 Int) (term!28 Int) (i!32 Int) (condition!36 Int) (substitutions!22 Int) (poly!24 Int) (hasSubstitution!38 Int) (index!29 Int) (its!31 Int) (changed!33 Int) (processedIndices!26 Int) (val!39 Int))
    (=> (and (not (= 1 1))
             ($main_inv1 substitutions!22 zeroPolynomials!23 poly!24 new_keys!25 processedIndices!26 varToPolyIndices!27 term!28 index!29 var!37 its!31 i!32 changed!33 var!37 hasSubstitution!38 condition!36 var!37 hasSubstitution!38 val!39))
        ($main_sum1 substitutions!22 zeroPolynomials!23 poly!24 new_keys!25 processedIndices!26 varToPolyIndices!27 term!28 index!29 var!37 its!31 i!32 changed!33 var!37 hasSubstitution!38 condition!36 var!37 hasSubstitution!38 val!39))))

; loop entry $main_inv2 (line 26)
(assert
  (forall ((var!37 Int) (varToPolyIndices!27 Int) (zeroPolynomials!23 Int) (new_keys!25 Int) (term!28 Int) (i!32 Int) (condition!36 Int) (substitutions!22 Int) (poly!24 Int) (hasSubstitution!38 Int) (index!29 Int) (its!31 Int) (changed!33 Int) (processedIndices!26 Int) (val!39 Int))
    (=> (and (= 1 1)
             ($main_inv1 substitutions!22 zeroPolynomials!23 poly!24 new_keys!25 processedIndices!26 varToPolyIndices!27 term!28 index!29 var!37 its!31 i!32 changed!33 var!37 hasSubstitution!38 condition!36 var!37 hasSubstitution!38 val!39))
        ($main_inv2 substitutions!22 zeroPolynomials!23 poly!24 new_keys!25 processedIndices!26 varToPolyIndices!27 term!28 index!29 var!37 its!31 i!32 changed!33 var!37 hasSubstitution!38 condition!36 var!37 hasSubstitution!38 val!39))))

; loop term $main_sum2 (line 26)
(assert
  (forall ((val!57 Int) (hasSubstitution!56 Int) (var!55 Int) (zeroPolynomials!41 Int) (term!46 Int) (poly!42 Int) (substitutions!40 Int) (new_keys!43 Int) (changed!51 Int) (its!49 Int) (index!47 Int) (processedIndices!44 Int) (varToPolyIndices!45 Int) (condition!54 Int) (i!50 Int))
    (=> (and (not (< i!50 zeroPolynomials!41))
             ($main_inv2 substitutions!40 zeroPolynomials!41 poly!42 new_keys!43 processedIndices!44 varToPolyIndices!45 term!46 index!47 var!55 its!49 i!50 changed!51 var!55 hasSubstitution!56 condition!54 var!55 hasSubstitution!56 val!57))
        ($main_sum2 substitutions!40 zeroPolynomials!41 poly!42 new_keys!43 processedIndices!44 varToPolyIndices!45 term!46 index!47 var!55 its!49 i!50 changed!51 var!55 hasSubstitution!56 condition!54 var!55 hasSubstitution!56 val!57))))

; if then
(assert
  (forall ((val!57 Int) (hasSubstitution!56 Int) (var!55 Int) (zeroPolynomials!41 Int) (term!46 Int) (poly!42 Int) (substitutions!40 Int) (new_keys!43 Int) (changed!51 Int) (its!49 Int) (index!47 Int) (processedIndices!44 Int) (varToPolyIndices!45 Int) (condition!54 Int) (i!50 Int))
    (=> (and (= poly!42 0)
             (< i!50 zeroPolynomials!41)
             ($main_inv2 substitutions!40 zeroPolynomials!41 poly!42 new_keys!43 processedIndices!44 varToPolyIndices!45 term!46 index!47 var!55 its!49 i!50 changed!51 var!55 hasSubstitution!56 condition!54 var!55 hasSubstitution!56 val!57))
        ($main_if2 substitutions!40 zeroPolynomials!41 poly!42 new_keys!43 processedIndices!44 varToPolyIndices!45 term!46 index!47 var!55 its!49 i!50 changed!51 var!55 hasSubstitution!56 condition!54 var!55 hasSubstitution!56 val!57 substitutions!40 zeroPolynomials!41 poly!42 new_keys!43 (+ processedIndices!44 1) varToPolyIndices!45 term!46 index!47 0 (+ its!49 1) (+ i!50 1) 1 0 hasSubstitution!56 condition!54 0 hasSubstitution!56 val!57))))

; if else
(assert
  (forall ((val!57 Int) (hasSubstitution!56 Int) (var!55 Int) (zeroPolynomials!41 Int) (term!46 Int) (poly!42 Int) (substitutions!40 Int) (new_keys!43 Int) (changed!51 Int) (its!49 Int) (index!47 Int) (processedIndices!44 Int) (varToPolyIndices!45 Int) (condition!54 Int) (i!50 Int))
    (=> (and (not (= poly!42 0))
             (< i!50 zeroPolynomials!41)
             ($main_inv2 substitutions!40 zeroPolynomials!41 poly!42 new_keys!43 processedIndices!44 varToPolyIndices!45 term!46 index!47 var!55 its!49 i!50 changed!51 var!55 hasSubstitution!56 condition!54 var!55 hasSubstitution!56 val!57))
        ($main_if2 substitutions!40 zeroPolynomials!41 poly!42 new_keys!43 processedIndices!44 varToPolyIndices!45 term!46 index!47 var!55 its!49 i!50 changed!51 var!55 hasSubstitution!56 condition!54 var!55 hasSubstitution!56 val!57 substitutions!40 zeroPolynomials!41 poly!42 new_keys!43 processedIndices!44 varToPolyIndices!45 term!46 index!47 0 (+ its!49 1) i!50 1 0 hasSubstitution!56 condition!54 0 hasSubstitution!56 val!57))))

; loop entry $main_inv3 (line 34)
(assert
  (forall ((val!57 Int) (changed!69 Int) (hasSubstitution!56 Int) (term!46 Int) (substitutions!40 Int) (zeroPolynomials!59 Int) (its!49 Int) (index!47 Int) (processedIndices!44 Int) (poly!60 Int) (term!64 Int) (var!55 Int) (zeroPolynomials!41 Int) (hasSubstitution!74 Int) (var!73 Int) (index!65 Int) (poly!42 Int) (substitutions!58 Int) (condition!72 Int) (its!67 Int) (varToPolyIndices!45 Int) (condition!54 Int) (i!50 Int) (processedIndices!62 Int) (new_keys!43 Int) (val!75 Int) (varToPolyIndices!63 Int) (changed!51 Int) (i!68 Int) (new_keys!61 Int))
    (=> (and ($main_if2 substitutions!40 zeroPolynomials!41 poly!42 new_keys!43 processedIndices!44 varToPolyIndices!45 term!46 index!47 var!55 its!49 i!50 changed!51 var!55 hasSubstitution!56 condition!54 var!55 hasSubstitution!56 val!57 substitutions!58 zeroPolynomials!59 poly!60 new_keys!61 processedIndices!62 varToPolyIndices!63 term!64 index!65 var!73 its!67 i!68 changed!69 var!73 hasSubstitution!74 condition!72 var!73 hasSubstitution!74 val!75))
        ($main_inv3 substitutions!58 zeroPolynomials!59 poly!60 new_keys!61 processedIndices!62 varToPolyIndices!63 term!64 index!65 var!73 its!67 i!68 changed!69 var!73 hasSubstitution!74 condition!72 var!73 hasSubstitution!74 val!75))))

; loop term $main_sum3 (line 34)
(assert
  (forall ((condition!90 Int) (poly!78 Int) (varToPolyIndices!81 Int) (processedIndices!80 Int) (index!83 Int) (zeroPolynomials!77 Int) (var!91 Int) (new_keys!79 Int) (its!85 Int) (substitutions!76 Int) (hasSubstitution!92 Int) (term!82 Int) (i!86 Int) (changed!87 Int) (val!93 Int))
    (=> (and (not (< term!82 poly!78))
             ($main_inv3 substitutions!76 zeroPolynomials!77 poly!78 new_keys!79 processedIndices!80 varToPolyIndices!81 term!82 index!83 var!91 its!85 i!86 changed!87 var!91 hasSubstitution!92 condition!90 var!91 hasSubstitution!92 val!93))
        ($main_sum3 substitutions!76 zeroPolynomials!77 poly!78 new_keys!79 processedIndices!80 varToPolyIndices!81 term!82 index!83 var!91 its!85 i!86 changed!87 var!91 hasSubstitution!92 condition!90 var!91 hasSubstitution!92 val!93))))

; forwards $main_inv3 (line 34)
(assert
  (forall ((condition!90 Int) (poly!78 Int) (varToPolyIndices!81 Int) (processedIndices!80 Int) (index!83 Int) (zeroPolynomials!77 Int) (var!91 Int) (new_keys!79 Int) (its!85 Int) (substitutions!76 Int) (hasSubstitution!92 Int) (term!82 Int) (i!86 Int) (changed!87 Int) (val!93 Int))
    (=> (and (< term!82 poly!78)
             ($main_inv3 substitutions!76 zeroPolynomials!77 poly!78 new_keys!79 processedIndices!80 varToPolyIndices!81 term!82 index!83 var!91 its!85 i!86 changed!87 var!91 hasSubstitution!92 condition!90 var!91 hasSubstitution!92 val!93))
        ($main_inv3 substitutions!76 zeroPolynomials!77 poly!78 new_keys!79 processedIndices!80 (+ varToPolyIndices!81 1) (+ term!82 1) index!83 var!91 its!85 i!86 changed!87 var!91 hasSubstitution!92 condition!90 var!91 hasSubstitution!92 val!93))))

; if then
(assert
  (forall ((val!57 Int) (zeroPolynomials!41 Int) (term!46 Int) (index!101 Int) (poly!96 Int) (poly!42 Int) (condition!108 Int) (substitutions!40 Int) (new_keys!43 Int) (val!111 Int) (hasSubstitution!110 Int) (processedIndices!44 Int) (hasSubstitution!56 Int) (zeroPolynomials!95 Int) (varToPolyIndices!99 Int) (processedIndices!98 Int) (var!55 Int) (varToPolyIndices!45 Int) (condition!54 Int) (i!50 Int) (term!100 Int) (var!109 Int) (substitutions!94 Int) (changed!51 Int) (new_keys!97 Int) (its!49 Int) (its!103 Int) (index!47 Int) (changed!105 Int) (i!104 Int))
    (=> (and (> hasSubstitution!110 0)
             (= var!109 term!100)
             (= poly!96 1)
             ($main_sum3 substitutions!94 zeroPolynomials!95 poly!96 new_keys!97 processedIndices!98 varToPolyIndices!99 term!100 index!101 var!109 its!103 i!104 changed!105 var!109 hasSubstitution!110 condition!108 var!109 hasSubstitution!110 val!111))
        ($main_if3 substitutions!40 zeroPolynomials!41 poly!42 new_keys!43 processedIndices!44 varToPolyIndices!45 term!46 index!47 var!55 its!49 i!50 changed!51 var!55 hasSubstitution!56 condition!54 var!55 hasSubstitution!56 val!57 (+ substitutions!94 1) zeroPolynomials!95 poly!96 (+ new_keys!97 1) processedIndices!98 varToPolyIndices!99 term!100 index!101 var!109 its!103 i!104 changed!105 var!109 hasSubstitution!110 condition!108 var!109 hasSubstitution!110 val!111))))

; if else
(assert
  (forall ((val!57 Int) (zeroPolynomials!41 Int) (term!46 Int) (index!101 Int) (poly!96 Int) (poly!42 Int) (condition!108 Int) (substitutions!40 Int) (new_keys!43 Int) (val!111 Int) (hasSubstitution!110 Int) (processedIndices!44 Int) (hasSubstitution!56 Int) (zeroPolynomials!95 Int) (varToPolyIndices!99 Int) (processedIndices!98 Int) (var!55 Int) (varToPolyIndices!45 Int) (condition!54 Int) (i!50 Int) (term!100 Int) (var!109 Int) (substitutions!94 Int) (changed!51 Int) (new_keys!97 Int) (its!49 Int) (its!103 Int) (index!47 Int) (changed!105 Int) (i!104 Int))
    (=> (and (not (> hasSubstitution!110 0))
             (= var!109 term!100)
             (= poly!96 1)
             ($main_sum3 substitutions!94 zeroPolynomials!95 poly!96 new_keys!97 processedIndices!98 varToPolyIndices!99 term!100 index!101 var!109 its!103 i!104 changed!105 var!109 hasSubstitution!110 condition!108 var!109 hasSubstitution!110 val!111))
        ($main_if3 substitutions!40 zeroPolynomials!41 poly!42 new_keys!43 processedIndices!44 varToPolyIndices!45 term!46 index!47 var!55 its!49 i!50 changed!51 var!55 hasSubstitution!56 condition!54 var!55 hasSubstitution!56 val!57 substitutions!94 zeroPolynomials!95 poly!96 new_keys!97 processedIndices!98 varToPolyIndices!99 term!100 index!101 var!109 its!103 i!104 changed!105 var!109 hasSubstitution!110 condition!108 var!109 hasSubstitution!110 val!111))))

; if then
(assert
  (forall ((val!57 Int) (zeroPolynomials!41 Int) (term!46 Int) (index!101 Int) (poly!96 Int) (poly!42 Int) (condition!108 Int) (substitutions!40 Int) (new_keys!43 Int) (val!111 Int) (hasSubstitution!110 Int) (processedIndices!44 Int) (hasSubstitution!56 Int) (zeroPolynomials!95 Int) (varToPolyIndices!99 Int) (processedIndices!98 Int) (var!55 Int) (varToPolyIndices!45 Int) (condition!54 Int) (i!50 Int) (term!100 Int) (var!109 Int) (substitutions!94 Int) (changed!51 Int) (new_keys!97 Int) (its!49 Int) (its!103 Int) (index!47 Int) (changed!105 Int) (i!104 Int))
    (=> (and (> hasSubstitution!110 0)
             (> condition!108 0)
             (not (= poly!96 1))
             ($main_sum3 substitutions!94 zeroPolynomials!95 poly!96 new_keys!97 processedIndices!98 varToPolyIndices!99 term!100 index!101 var!109 its!103 i!104 changed!105 var!109 hasSubstitution!110 condition!108 var!109 hasSubstitution!110 val!111))
        ($main_if4 substitutions!40 zeroPolynomials!41 poly!42 new_keys!43 processedIndices!44 varToPolyIndices!45 term!46 index!47 var!55 its!49 i!50 changed!51 var!55 hasSubstitution!56 condition!54 var!55 hasSubstitution!56 val!57 (+ substitutions!94 1) zeroPolynomials!95 poly!96 (+ new_keys!97 1) processedIndices!98 varToPolyIndices!99 term!100 index!101 var!109 its!103 i!104 0 var!109 hasSubstitution!110 condition!108 var!109 hasSubstitution!110 val!111))))

; if else
(assert
  (forall ((val!57 Int) (zeroPolynomials!41 Int) (term!46 Int) (index!101 Int) (poly!96 Int) (poly!42 Int) (condition!108 Int) (substitutions!40 Int) (new_keys!43 Int) (val!111 Int) (hasSubstitution!110 Int) (processedIndices!44 Int) (hasSubstitution!56 Int) (zeroPolynomials!95 Int) (varToPolyIndices!99 Int) (processedIndices!98 Int) (var!55 Int) (varToPolyIndices!45 Int) (condition!54 Int) (i!50 Int) (term!100 Int) (var!109 Int) (substitutions!94 Int) (changed!51 Int) (new_keys!97 Int) (its!49 Int) (its!103 Int) (index!47 Int) (changed!105 Int) (i!104 Int))
    (=> (and (not (> hasSubstitution!110 0))
             (> condition!108 0)
             (not (= poly!96 1))
             ($main_sum3 substitutions!94 zeroPolynomials!95 poly!96 new_keys!97 processedIndices!98 varToPolyIndices!99 term!100 index!101 var!109 its!103 i!104 changed!105 var!109 hasSubstitution!110 condition!108 var!109 hasSubstitution!110 val!111))
        ($main_if4 substitutions!40 zeroPolynomials!41 poly!42 new_keys!43 processedIndices!44 varToPolyIndices!45 term!46 index!47 var!55 its!49 i!50 changed!51 var!55 hasSubstitution!56 condition!54 var!55 hasSubstitution!56 val!57 substitutions!94 zeroPolynomials!95 poly!96 new_keys!97 processedIndices!98 varToPolyIndices!99 term!100 index!101 var!109 its!103 i!104 0 var!109 hasSubstitution!110 condition!108 var!109 hasSubstitution!110 val!111))))

; if then
(assert
  (forall ((condition!144 Int) (poly!132 Int) (var!55 Int) (zeroPolynomials!41 Int) (term!46 Int) (hasSubstitution!146 Int) (substitutions!40 Int) (changed!141 Int) (new_keys!43 Int) (index!47 Int) (val!57 Int) (var!145 Int) (hasSubstitution!56 Int) (its!139 Int) (term!136 Int) (poly!42 Int) (varToPolyIndices!45 Int) (condition!54 Int) (i!50 Int) (i!140 Int) (zeroPolynomials!131 Int) (changed!51 Int) (processedIndices!134 Int) (its!49 Int) (varToPolyIndices!135 Int) (processedIndices!44 Int) (new_keys!133 Int) (val!147 Int) (substitutions!130 Int) (index!137 Int))
    (=> (and ($main_if4 substitutions!40 zeroPolynomials!41 poly!42 new_keys!43 processedIndices!44 varToPolyIndices!45 term!46 index!47 var!55 its!49 i!50 changed!51 var!55 hasSubstitution!56 condition!54 var!55 hasSubstitution!56 val!57 substitutions!130 zeroPolynomials!131 poly!132 new_keys!133 processedIndices!134 varToPolyIndices!135 term!136 index!137 var!145 its!139 i!140 changed!141 var!145 hasSubstitution!146 condition!144 var!145 hasSubstitution!146 val!147))
        ($main_if5 substitutions!40 zeroPolynomials!41 poly!42 new_keys!43 processedIndices!44 varToPolyIndices!45 term!46 index!47 var!55 its!49 i!50 changed!51 var!55 hasSubstitution!56 condition!54 var!55 hasSubstitution!56 val!57 substitutions!130 zeroPolynomials!131 poly!132 new_keys!133 (+ processedIndices!134 1) (- varToPolyIndices!135 1) term!136 index!137 var!145 its!139 (+ i!140 1) changed!141 var!145 hasSubstitution!146 condition!144 var!145 hasSubstitution!146 val!147))))

; if else
(assert
  (forall ((val!57 Int) (zeroPolynomials!41 Int) (term!46 Int) (index!101 Int) (poly!96 Int) (poly!42 Int) (condition!108 Int) (substitutions!40 Int) (new_keys!43 Int) (val!111 Int) (hasSubstitution!110 Int) (processedIndices!44 Int) (hasSubstitution!56 Int) (zeroPolynomials!95 Int) (varToPolyIndices!99 Int) (processedIndices!98 Int) (var!55 Int) (varToPolyIndices!45 Int) (condition!54 Int) (i!50 Int) (term!100 Int) (var!109 Int) (substitutions!94 Int) (changed!51 Int) (new_keys!97 Int) (its!49 Int) (its!103 Int) (index!47 Int) (changed!105 Int) (i!104 Int))
    (=> (and (not (> condition!108 0))
             (not (= poly!96 1))
             ($main_sum3 substitutions!94 zeroPolynomials!95 poly!96 new_keys!97 processedIndices!98 varToPolyIndices!99 term!100 index!101 var!109 its!103 i!104 changed!105 var!109 hasSubstitution!110 condition!108 var!109 hasSubstitution!110 val!111))
        ($main_if5 substitutions!40 zeroPolynomials!41 poly!42 new_keys!43 processedIndices!44 varToPolyIndices!45 term!46 index!47 var!55 its!49 i!50 changed!51 var!55 hasSubstitution!56 condition!54 var!55 hasSubstitution!56 val!57 substitutions!94 zeroPolynomials!95 poly!96 new_keys!97 processedIndices!98 varToPolyIndices!99 term!100 index!101 var!109 its!103 (+ i!104 1) changed!105 var!109 hasSubstitution!110 condition!108 var!109 hasSubstitution!110 val!111))))

; if then
(assert
  (forall ((changed!123 Int) (poly!114 Int) (hasSubstitution!56 Int) (var!55 Int) (zeroPolynomials!41 Int) (term!46 Int) (i!122 Int) (new_keys!43 Int) (hasSubstitution!128 Int) (index!47 Int) (processedIndices!44 Int) (val!57 Int) (zeroPolynomials!113 Int) (processedIndices!116 Int) (varToPolyIndices!117 Int) (term!118 Int) (condition!126 Int) (substitutions!112 Int) (poly!42 Int) (substitutions!40 Int) (its!121 Int) (varToPolyIndices!45 Int) (condition!54 Int) (i!50 Int) (var!127 Int) (changed!51 Int) (index!119 Int) (its!49 Int) (val!129 Int) (new_keys!115 Int))
    (=> (and ($main_if3 substitutions!40 zeroPolynomials!41 poly!42 new_keys!43 processedIndices!44 varToPolyIndices!45 term!46 index!47 var!55 its!49 i!50 changed!51 var!55 hasSubstitution!56 condition!54 var!55 hasSubstitution!56 val!57 substitutions!112 zeroPolynomials!113 poly!114 new_keys!115 processedIndices!116 varToPolyIndices!117 term!118 index!119 var!127 its!121 i!122 changed!123 var!127 hasSubstitution!128 condition!126 var!127 hasSubstitution!128 val!129))
        ($main_if6 substitutions!40 zeroPolynomials!41 poly!42 new_keys!43 processedIndices!44 varToPolyIndices!45 term!46 index!47 var!55 its!49 i!50 changed!51 var!55 hasSubstitution!56 condition!54 var!55 hasSubstitution!56 val!57 substitutions!112 zeroPolynomials!113 poly!114 new_keys!115 (+ processedIndices!116 1) (- varToPolyIndices!117 1) term!118 index!119 var!127 its!121 (+ i!122 1) changed!123 var!127 hasSubstitution!128 condition!126 var!127 hasSubstitution!128 val!129))))

; if else
(assert
  (forall ((var!163 Int) (new_keys!151 Int) (hasSubstitution!56 Int) (var!55 Int) (zeroPolynomials!41 Int) (varToPolyIndices!153 Int) (substitutions!148 Int) (poly!42 Int) (new_keys!43 Int) (changed!51 Int) (changed!159 Int) (index!155 Int) (its!49 Int) (processedIndices!44 Int) (processedIndices!152 Int) (zeroPolynomials!149 Int) (val!57 Int) (val!165 Int) (condition!162 Int) (its!157 Int) (term!46 Int) (term!154 Int) (poly!150 Int) (substitutions!40 Int) (hasSubstitution!164 Int) (varToPolyIndices!45 Int) (condition!54 Int) (i!50 Int) (i!158 Int) (index!47 Int))
    (=> (and ($main_if5 substitutions!40 zeroPolynomials!41 poly!42 new_keys!43 processedIndices!44 varToPolyIndices!45 term!46 index!47 var!55 its!49 i!50 changed!51 var!55 hasSubstitution!56 condition!54 var!55 hasSubstitution!56 val!57 substitutions!148 zeroPolynomials!149 poly!150 new_keys!151 processedIndices!152 varToPolyIndices!153 term!154 index!155 var!163 its!157 i!158 changed!159 var!163 hasSubstitution!164 condition!162 var!163 hasSubstitution!164 val!165))
        ($main_if6 substitutions!40 zeroPolynomials!41 poly!42 new_keys!43 processedIndices!44 varToPolyIndices!45 term!46 index!47 var!55 its!49 i!50 changed!51 var!55 hasSubstitution!56 condition!54 var!55 hasSubstitution!56 val!57 substitutions!148 zeroPolynomials!149 poly!150 new_keys!151 processedIndices!152 varToPolyIndices!153 term!154 index!155 var!163 its!157 i!158 changed!159 var!163 hasSubstitution!164 condition!162 var!163 hasSubstitution!164 val!165))))

; forwards $main_inv2 (line 26)
(assert
  (forall ((hasSubstitution!182 Int) (var!55 Int) (term!46 Int) (condition!180 Int) (poly!42 Int) (substitutions!40 Int) (changed!51 Int) (term!172 Int) (its!49 Int) (processedIndices!44 Int) (processedIndices!170 Int) (changed!177 Int) (val!57 Int) (its!175 Int) (new_keys!169 Int) (varToPolyIndices!171 Int) (val!183 Int) (index!173 Int) (hasSubstitution!56 Int) (i!176 Int) (var!181 Int) (zeroPolynomials!41 Int) (zeroPolynomials!167 Int) (varToPolyIndices!45 Int) (condition!54 Int) (i!50 Int) (poly!168 Int) (new_keys!43 Int) (substitutions!166 Int) (index!47 Int))
    (=> (and ($main_if6 substitutions!40 zeroPolynomials!41 poly!42 new_keys!43 processedIndices!44 varToPolyIndices!45 term!46 index!47 var!55 its!49 i!50 changed!51 var!55 hasSubstitution!56 condition!54 var!55 hasSubstitution!56 val!57 substitutions!166 zeroPolynomials!167 poly!168 new_keys!169 processedIndices!170 varToPolyIndices!171 term!172 index!173 var!181 its!175 i!176 changed!177 var!181 hasSubstitution!182 condition!180 var!181 hasSubstitution!182 val!183))
        ($main_inv2 substitutions!166 zeroPolynomials!167 poly!168 new_keys!169 processedIndices!170 varToPolyIndices!171 0 index!173 var!181 its!175 i!176 changed!177 var!181 hasSubstitution!182 condition!180 var!181 hasSubstitution!182 val!183))))

; loop entry $main_inv4 (line 71)
(assert
  (forall ((term!190 Int) (val!201 Int) (zeroPolynomials!185 Int) (var!199 Int) (varToPolyIndices!189 Int) (condition!198 Int) (substitutions!184 Int) (hasSubstitution!200 Int) (changed!195 Int) (index!191 Int) (processedIndices!188 Int) (new_keys!187 Int) (its!193 Int) (i!194 Int) (poly!186 Int))
    (=> (and ($main_sum2 substitutions!184 zeroPolynomials!185 poly!186 new_keys!187 processedIndices!188 varToPolyIndices!189 term!190 index!191 var!199 its!193 i!194 changed!195 var!199 hasSubstitution!200 condition!198 var!199 hasSubstitution!200 val!201))
        ($main_inv4 substitutions!184 zeroPolynomials!185 poly!186 new_keys!187 processedIndices!188 varToPolyIndices!189 term!190 index!191 var!199 its!193 i!194 changed!195 var!199 hasSubstitution!200 condition!198 var!199 hasSubstitution!200 val!201))))

; loop term $main_sum4 (line 71)
(assert
  (forall ((condition!216 Int) (substitutions!202 Int) (val!219 Int) (new_keys!205 Int) (term!208 Int) (var!217 Int) (its!211 Int) (varToPolyIndices!207 Int) (changed!213 Int) (hasSubstitution!218 Int) (zeroPolynomials!203 Int) (processedIndices!206 Int) (i!212 Int) (poly!204 Int) (index!209 Int))
    (=> (and (not (< var!217 new_keys!205))
             ($main_inv4 substitutions!202 zeroPolynomials!203 poly!204 new_keys!205 processedIndices!206 varToPolyIndices!207 term!208 index!209 var!217 its!211 i!212 changed!213 var!217 hasSubstitution!218 condition!216 var!217 hasSubstitution!218 val!219))
        ($main_sum4 substitutions!202 zeroPolynomials!203 poly!204 new_keys!205 processedIndices!206 varToPolyIndices!207 term!208 index!209 var!217 its!211 i!212 changed!213 var!217 hasSubstitution!218 condition!216 var!217 hasSubstitution!218 val!219))))

; loop entry $main_inv5 (line 72)
(assert
  (forall ((condition!216 Int) (substitutions!202 Int) (val!219 Int) (new_keys!205 Int) (term!208 Int) (var!217 Int) (its!211 Int) (varToPolyIndices!207 Int) (changed!213 Int) (hasSubstitution!218 Int) (zeroPolynomials!203 Int) (processedIndices!206 Int) (i!212 Int) (poly!204 Int) (index!209 Int))
    (=> (and (< var!217 new_keys!205)
             ($main_inv4 substitutions!202 zeroPolynomials!203 poly!204 new_keys!205 processedIndices!206 varToPolyIndices!207 term!208 index!209 var!217 its!211 i!212 changed!213 var!217 hasSubstitution!218 condition!216 var!217 hasSubstitution!218 val!219))
        ($main_inv5 substitutions!202 zeroPolynomials!203 poly!204 new_keys!205 processedIndices!206 varToPolyIndices!207 term!208 index!209 var!217 its!211 i!212 changed!213 var!217 hasSubstitution!218 condition!216 var!217 hasSubstitution!218 val!219))))

; loop term $main_sum5 (line 72)
(assert
  (forall ((new_keys!223 Int) (condition!234 Int) (its!229 Int) (varToPolyIndices!225 Int) (substitutions!220 Int) (val!237 Int) (var!235 Int) (term!226 Int) (poly!222 Int) (index!227 Int) (hasSubstitution!236 Int) (zeroPolynomials!221 Int) (processedIndices!224 Int) (i!230 Int) (changed!231 Int))
    (=> (and (not (< index!227 varToPolyIndices!225))
             ($main_inv5 substitutions!220 zeroPolynomials!221 poly!222 new_keys!223 processedIndices!224 varToPolyIndices!225 term!226 index!227 var!235 its!229 i!230 changed!231 var!235 hasSubstitution!236 condition!234 var!235 hasSubstitution!236 val!237))
        ($main_sum5 substitutions!220 zeroPolynomials!221 poly!222 new_keys!223 processedIndices!224 varToPolyIndices!225 term!226 index!227 var!235 its!229 i!230 changed!231 var!235 hasSubstitution!236 condition!234 var!235 hasSubstitution!236 val!237))))

; forwards $main_inv5 (line 72)
(assert
  (forall ((new_keys!223 Int) (condition!234 Int) (its!229 Int) (varToPolyIndices!225 Int) (substitutions!220 Int) (val!237 Int) (var!235 Int) (term!226 Int) (poly!222 Int) (index!227 Int) (hasSubstitution!236 Int) (zeroPolynomials!221 Int) (processedIndices!224 Int) (i!230 Int) (changed!231 Int))
    (=> (and (< index!227 varToPolyIndices!225)
             ($main_inv5 substitutions!220 zeroPolynomials!221 poly!222 new_keys!223 processedIndices!224 varToPolyIndices!225 term!226 index!227 var!235 its!229 i!230 changed!231 var!235 hasSubstitution!236 condition!234 var!235 hasSubstitution!236 val!237))
        ($main_inv5 substitutions!220 zeroPolynomials!221 poly!222 new_keys!223 processedIndices!224 varToPolyIndices!225 term!226 (+ index!227 1) var!235 its!229 i!230 changed!231 var!235 hasSubstitution!236 condition!234 var!235 hasSubstitution!236 val!237))))

; forwards $main_inv4 (line 71)
(assert
  (forall ((condition!252 Int) (poly!240 Int) (index!245 Int) (changed!249 Int) (i!248 Int) (new_keys!241 Int) (hasSubstitution!254 Int) (varToPolyIndices!243 Int) (its!247 Int) (var!253 Int) (term!244 Int) (val!255 Int) (processedIndices!242 Int) (substitutions!238 Int) (zeroPolynomials!239 Int))
    (=> (and ($main_sum5 substitutions!238 zeroPolynomials!239 poly!240 new_keys!241 processedIndices!242 varToPolyIndices!243 term!244 index!245 var!253 its!247 i!248 changed!249 var!253 hasSubstitution!254 condition!252 var!253 hasSubstitution!254 val!255))
        ($main_inv4 substitutions!238 zeroPolynomials!239 poly!240 new_keys!241 processedIndices!242 varToPolyIndices!243 term!244 index!245 (+ var!253 2) its!247 i!248 changed!249 (+ var!253 2) hasSubstitution!254 condition!252 (+ var!253 2) hasSubstitution!254 val!255))))

; break $main_sum1
(assert
  (forall ((varToPolyIndices!261 Int) (val!273 Int) (zeroPolynomials!257 Int) (i!266 Int) (processedIndices!260 Int) (hasSubstitution!272 Int) (poly!258 Int) (its!265 Int) (var!271 Int) (condition!270 Int) (term!262 Int) (substitutions!256 Int) (new_keys!259 Int) (changed!267 Int) (index!263 Int))
    (=> (and (= changed!267 0)
             ($main_sum4 substitutions!256 zeroPolynomials!257 poly!258 new_keys!259 processedIndices!260 varToPolyIndices!261 term!262 index!263 var!271 its!265 i!266 changed!267 var!271 hasSubstitution!272 condition!270 var!271 hasSubstitution!272 val!273))
        ($main_sum1 substitutions!256 zeroPolynomials!257 poly!258 new_keys!259 processedIndices!260 varToPolyIndices!261 term!262 index!263 var!271 its!265 0 changed!267 var!271 hasSubstitution!272 condition!270 var!271 hasSubstitution!272 val!273))))

; if else
(assert
  (forall ((varToPolyIndices!261 Int) (var!37 Int) (zeroPolynomials!23 Int) (new_keys!25 Int) (term!28 Int) (zeroPolynomials!257 Int) (condition!36 Int) (processedIndices!260 Int) (poly!258 Int) (its!265 Int) (index!29 Int) (its!31 Int) (changed!33 Int) (val!273 Int) (varToPolyIndices!27 Int) (i!266 Int) (i!32 Int) (substitutions!22 Int) (hasSubstitution!272 Int) (processedIndices!26 Int) (val!39 Int) (term!262 Int) (substitutions!256 Int) (var!271 Int) (poly!24 Int) (hasSubstitution!38 Int) (condition!270 Int) (new_keys!259 Int) (changed!267 Int) (index!263 Int))
    (=> (and (not (= changed!267 0))
             ($main_sum4 substitutions!256 zeroPolynomials!257 poly!258 new_keys!259 processedIndices!260 varToPolyIndices!261 term!262 index!263 var!271 its!265 i!266 changed!267 var!271 hasSubstitution!272 condition!270 var!271 hasSubstitution!272 val!273))
        ($main_if7 substitutions!22 zeroPolynomials!23 poly!24 new_keys!25 processedIndices!26 varToPolyIndices!27 term!28 index!29 var!37 its!31 i!32 changed!33 var!37 hasSubstitution!38 condition!36 var!37 hasSubstitution!38 val!39 substitutions!256 zeroPolynomials!257 poly!258 new_keys!259 processedIndices!260 varToPolyIndices!261 term!262 index!263 var!271 its!265 0 changed!267 var!271 hasSubstitution!272 condition!270 var!271 hasSubstitution!272 val!273))))

; forwards $main_inv1 (line 25)
(assert
  (forall ((changed!285 Int) (varToPolyIndices!27 Int) (term!280 Int) (zeroPolynomials!23 Int) (term!28 Int) (substitutions!274 Int) (i!32 Int) (condition!36 Int) (var!289 Int) (zeroPolynomials!275 Int) (poly!276 Int) (hasSubstitution!290 Int) (new_keys!277 Int) (poly!24 Int) (index!29 Int) (its!31 Int) (condition!288 Int) (var!37 Int) (val!291 Int) (new_keys!25 Int) (index!281 Int) (substitutions!22 Int) (processedIndices!278 Int) (its!283 Int) (processedIndices!26 Int) (val!39 Int) (hasSubstitution!38 Int) (i!284 Int) (changed!33 Int) (varToPolyIndices!279 Int))
    (=> (and ($main_if7 substitutions!22 zeroPolynomials!23 poly!24 new_keys!25 processedIndices!26 varToPolyIndices!27 term!28 index!29 var!37 its!31 i!32 changed!33 var!37 hasSubstitution!38 condition!36 var!37 hasSubstitution!38 val!39 substitutions!274 zeroPolynomials!275 poly!276 new_keys!277 processedIndices!278 varToPolyIndices!279 term!280 index!281 var!289 its!283 i!284 changed!285 var!289 hasSubstitution!290 condition!288 var!289 hasSubstitution!290 val!291))
        ($main_inv1 substitutions!274 zeroPolynomials!275 poly!276 new_keys!277 processedIndices!278 varToPolyIndices!279 term!280 index!281 var!289 its!283 i!284 changed!285 var!289 hasSubstitution!290 condition!288 var!289 hasSubstitution!290 val!291))))

; VERIFIER_assert (< its!301 20)
(assert
  (forall ((condition!306 Int) (val!309 Int) (index!299 Int) (processedIndices!296 Int) (poly!294 Int) (its!301 Int) (term!298 Int) (i!302 Int) (changed!303 Int) (varToPolyIndices!297 Int) (var!307 Int) (hasSubstitution!308 Int) (substitutions!292 Int) (zeroPolynomials!293 Int) (new_keys!295 Int))
    (=> (and (not (< its!301 20))
             ($main_sum1 substitutions!292 zeroPolynomials!293 poly!294 new_keys!295 processedIndices!296 varToPolyIndices!297 term!298 index!299 var!307 its!301 i!302 changed!303 var!307 hasSubstitution!308 condition!306 var!307 hasSubstitution!308 val!309))
        false)))

(check-sat)
