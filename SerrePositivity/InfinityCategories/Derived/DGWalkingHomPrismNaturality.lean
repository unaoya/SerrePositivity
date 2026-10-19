module
public import SerrePositivity.InfinityCategories.Derived.DGWalkingHomMapPinched
public import SerrePositivity.InfinityCategories.Derived.DGWalkingHomPinched
public import SerrePositivity.InfinityCategories.Derived.DGWalkingHomRefinementNaturality
public import SerrePositivity.InfinityCategories.Derived.DGStrictNatTransComponentExt
public import SerrePositivity.InfinityCategories.Derived.DGStrictNatTransSimplexWhisker
public import SerrePositivity.DifferentialGraded.Functor.QuasiIsoHomology

/-! # 自由 Hom の閉細分 prism の全単体の自然性

概要：閉前合成の厳密自然変換の二相単体は、dg 関手像の係数変換と可換。
方針：両相の評価関手の等式、閉射の像、恒等元の像を成分比較へ渡す。
規約：全次数・全係数・全時刻。使われ方：実屋根の商比較の固定標的部分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D E : Type v) [DGCategory A D] [DGCategory A E]
variable [Small.{u} D] [Small.{u} E] (Q : DGFunctor A D E)

/-- 閉前合成の両相と全成分は、dg 関手像の自由係数へ厳密に自然。 -/
lemma dgWalkingHomPrecomposeNatTrans_naturality {p q : D} (y : D)
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q) :
    HEq (dgStrictNatTransPostcomp (dgWalkingHomPrecomposeNatTrans A D y r) Q)
      (dgStrictNatTransPrecomp (dgWalkingHomMap A (Q.map q y))
        (dgWalkingHomPrecomposeNatTrans A E (Q.obj y) (Q.onClosed.map r))) := by
  apply dgStrictNatTrans_hext
    _ _ (dgWalkingHomRefinedEvaluation_naturality A D E Q y r)
      (dgWalkingHomOriginalEvaluation_naturality A D E Q q y)
  rintro ⟨x⟩
  cases x
  · exact heq_of_eq (Q.closedHomEquiv_map r).symm
  · apply heq_of_eq
    apply Subtype.ext
    exact DGFunctor.map_unitElement A Q y

/-- 自由係数の全二相単体は、商側の係数変換を経た二相単体へ写る。 -/
lemma dgWalkingHomPrecompose_simplex_naturality {p q : D} (y : D)
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q)
    {n : ℕ} (s : Simplex A (DGWalkingHom.{u, v} A (homObject A D q y)) n)
    (β : Fin (n + 1) →o Fin 2) :
    ((dgWalkingHomPrecomposeNatTrans A D y r).simplex s β).map Q =
      (dgWalkingHomPrecomposeNatTrans A E (Q.obj y) (Q.onClosed.map r)).simplex
        (s.map (dgWalkingHomMap A (Q.map q y))) β := by
  have h := dgWalkingHomPrecomposeNatTrans_naturality A D E Q y r
  have hF := dgWalkingHomRefinedEvaluation_naturality A D E Q y r
  have hG := dgWalkingHomOriginalEvaluation_naturality A D E Q q y
  have he := dgStrictNatTrans_simplex_eq_of_heq _ _ hF hG h s β
  exact (dgStrictNatTransPostcomp_simplex _ Q s β).symm.trans
    (he.trans (dgStrictNatTransPrecomp_simplex _ _ s β))

/-- 元の全係数を含めた二相単体は、Hom 鎖写像による係数像の二相単体へ写る。 -/
lemma dgWalkingHomPrecompose_coefficient_naturality {p q : D} (y : D)
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q)
    {n : ℕ} (s : (DGNerve.pinchedHom A D q y).obj (Opposite.op ⟨n⟩))
    (β : Fin (n + 2) →o Fin 2) :
    ((dgWalkingHomPrecomposeNatTrans A D y r).simplex
      ((dgWalkingHomPinched A D q y).app _ s).val β).map Q =
      (dgWalkingHomPrecomposeNatTrans A E (Q.obj y) (Q.onClosed.map r)).simplex
        ((dgWalkingHomPinched A E (Q.obj q) (Q.obj y)).app _
          ((pinchedHomChainMap (Q.map q y)).app _ s)).val β := by
  have hc := congrArg (fun f => (f.app (Opposite.op ⟨n⟩) s).val)
    (dgWalkingHomMap_pinched A (Q.map q y))
  have hv := (dgFunctorPinchedChainMap_val A (dgWalkingHomMap A (Q.map q y))
    ((dgWalkingHomPinched A D q y).app _ s)).symm.trans hc
  exact (dgWalkingHomPrecompose_simplex_naturality A D E Q y r _ β).trans
    (congrArg (fun t =>
      (dgWalkingHomPrecomposeNatTrans A E (Q.obj y) (Q.onClosed.map r)).simplex t β) hv)

end SerrePositivity.InfinityCategories
