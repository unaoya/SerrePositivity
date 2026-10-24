module
public import SerrePositivity.InfinityCategories.Derived.DGWalkingHomMapPinched
public import SerrePositivity.InfinityCategories.Derived.DGWalkingHomPinchedGeneral
public import SerrePositivity.InfinityCategories.Derived.DGWalkingHomRefinementDirectNaturality
public import SerrePositivity.InfinityCategories.Derived.DGStrictNatTransComponentExt
public import SerrePositivity.InfinityCategories.Derived.DGStrictNatTransSimplexWhisker

/-!
概要：自由 Hom の直接前合成 prism の全係数自然性を示す。
方針：直接の閉前合成鎖写像と全二相単体の係数比較を使う。
規約：始域・標的の Small 仮定なしに、元の対象と全係数を保持する。
使われ方：D2 の一般対象宇宙での dg gluing 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D E : Type v) [DGCategory A D] [DGCategory A E]
variable (Q : DGFunctor A D E)

/-- 概要：閉前合成の両相と全成分は、dg 関手像の自由係数へ厳密に自然。
方針：直接の閉前合成と自由 Hom の生成辺を使う。
規約：Small 仮定を加えず、全係数と指定時刻を保持する。
使われ方：一般対象宇宙の係数比較と既存版との一致。 -/
lemma dgWalkingHomPrecomposeNatTransDirect_naturality {p q : D} (y : D)
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q) :
    HEq (dgStrictNatTransPostcomp (dgWalkingHomPrecomposeNatTransDirect A D y r) Q)
      (dgStrictNatTransPrecomp (dgWalkingHomMap A (Q.map q y))
        (dgWalkingHomPrecomposeNatTransDirect A E (Q.obj y) (Q.onClosed.map r))) := by
  apply dgStrictNatTrans_hext
    _ _ (dgWalkingHomRefinedEvaluationDirect_naturality A D E Q y r)
      (dgWalkingHomOriginalEvaluationDirect_naturality A D E Q q y)
  rintro ⟨x⟩
  cases x
  · exact heq_of_eq (Q.closedHomEquiv_map r).symm
  · apply heq_of_eq
    apply Subtype.ext
    exact DGFunctor.map_unitElement A Q y

/-- 概要：自由係数の全二相単体は、商側の係数変換を経た二相単体へ写る。
方針：直接の閉前合成と自由 Hom の生成辺を使う。
規約：Small 仮定を加えず、全係数と指定時刻を保持する。
使われ方：一般対象宇宙の係数比較と既存版との一致。 -/
lemma dgWalkingHomPrecomposeDirect_simplex_naturality {p q : D} (y : D)
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q)
    {n : ℕ} (s : Simplex A (DGWalkingHom.{u, v} A (homObject A D q y)) n)
    (β : Fin (n + 1) →o Fin 2) :
    ((dgWalkingHomPrecomposeNatTransDirect A D y r).simplex s β).map Q =
      (dgWalkingHomPrecomposeNatTransDirect A E (Q.obj y) (Q.onClosed.map r)).simplex
        (s.map (dgWalkingHomMap A (Q.map q y))) β := by
  have h := dgWalkingHomPrecomposeNatTransDirect_naturality A D E Q y r
  have hF := dgWalkingHomRefinedEvaluationDirect_naturality A D E Q y r
  have hG := dgWalkingHomOriginalEvaluationDirect_naturality A D E Q q y
  have he := dgStrictNatTrans_simplex_eq_of_heq _ _ hF hG h s β
  exact (dgStrictNatTransPostcomp_simplex _ Q s β).symm.trans
    (he.trans (dgStrictNatTransPrecomp_simplex _ _ s β))

/-- 概要：元の全係数を含めた二相単体は、Hom 鎖写像による係数像の二相単体へ写る。
方針：直接の閉前合成と自由 Hom の生成辺を使う。
規約：Small 仮定を加えず、全係数と指定時刻を保持する。
使われ方：一般対象宇宙の係数比較と既存版との一致。 -/
lemma dgWalkingHomPrecomposeDirect_coefficient_naturality {p q : D} (y : D)
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q)
    {n : ℕ} (s : (DGNerve.pinchedHom A D q y).obj (Opposite.op ⟨n⟩))
    (β : Fin (n + 2) →o Fin 2) :
    ((dgWalkingHomPrecomposeNatTransDirect A D y r).simplex
      ((dgWalkingHomPinched A D q y).app _ s).val β).map Q =
      (dgWalkingHomPrecomposeNatTransDirect A E (Q.obj y) (Q.onClosed.map r)).simplex
        ((dgWalkingHomPinched A E (Q.obj q) (Q.obj y)).app _
          ((pinchedHomChainMap (Q.map q y)).app _ s)).val β := by
  have hc := congrArg (fun f => (f.app (Opposite.op ⟨n⟩) s).val)
    (dgWalkingHomMap_pinched A (Q.map q y))
  have hv := (dgFunctorPinchedChainMap_val A (dgWalkingHomMap A (Q.map q y))
    ((dgWalkingHomPinched A D q y).app _ s)).symm.trans hc
  exact (dgWalkingHomPrecomposeDirect_simplex_naturality A D E Q y r _ β).trans
    (congrArg (fun t =>
      (dgWalkingHomPrecomposeNatTransDirect A E (Q.obj y) (Q.onClosed.map r)).simplex t β) hv)

end SerrePositivity.InfinityCategories
