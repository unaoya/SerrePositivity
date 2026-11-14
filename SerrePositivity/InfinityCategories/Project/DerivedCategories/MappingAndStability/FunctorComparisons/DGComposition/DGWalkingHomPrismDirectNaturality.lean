module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.DGWalkingHomMapPinched
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.DGWalkingHomPinchedGeneral
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGComposition.DGWalkingHomRefinementDirectNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGStrictNatTransComponentExt
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGStrictNatTransSimplexWhisker

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E]
variable (Q : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)

/-- 概要：閉前合成の両相と全成分は、dg 関手像の自由係数へ厳密に自然。
方針：直接の閉前合成と自由 Hom の生成辺を使う。
規約：Small 仮定を加えず、全係数と指定時刻を保持する。
使われ方：一般対象宇宙の係数比較と既存版との一致。 -/
lemma dgWalkingHomPrecomposeNatTransDirect_naturality {p q : D} (y : D)
    (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPrecomposeNatTransDirect A D y r) Q)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPrecomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomMap A (Q.map q y))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPrecomposeNatTransDirect A E (Q.obj y) (Q.onClosed.map r))) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTrans_hext
    _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomRefinedEvaluationDirect_naturality A D E Q y r)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomOriginalEvaluationDirect_naturality A D E Q q y)
  rintro ⟨x⟩
  cases x
  · exact heq_of_eq (Q.closedHomEquiv_map r).symm
  · apply heq_of_eq
    apply Subtype.ext
    exact _root_.SerrePositivity.DifferentialGraded.DGFunctor.map_unitElement A Q y

/-- 概要：自由係数の全二相単体は、商側の係数変換を経た二相単体へ写る。
方針：直接の閉前合成と自由 Hom の生成辺を使う。
規約：Small 仮定を加えず、全係数と指定時刻を保持する。
使われ方：一般対象宇宙の係数比較と既存版との一致。 -/
lemma dgWalkingHomPrecomposeDirect_simplex_naturality {p q : D} (y : D)
    (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q)
    {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHom.{u, v} A (homObject A D q y)) n)
    (β : Fin (n + 1) →o Fin 2) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPrecomposeNatTransDirect A D y r).simplex s β).map Q =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPrecomposeNatTransDirect A E (Q.obj y) (Q.onClosed.map r)).simplex
        (s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomMap A (Q.map q y))) β := by
  have h := dgWalkingHomPrecomposeNatTransDirect_naturality A D E Q y r
  have hF := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomRefinedEvaluationDirect_naturality A D E Q y r
  have hG := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomOriginalEvaluationDirect_naturality A D E Q q y
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTrans_simplex_eq_of_heq _ _ hF hG h s β
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp_simplex _ Q s β).symm.trans
    (he.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPrecomp_simplex _ _ s β))

/-- 概要：元の全係数を含めた二相単体は、Hom 鎖写像による係数像の二相単体へ写る。
方針：直接の閉前合成と自由 Hom の生成辺を使う。
規約：Small 仮定を加えず、全係数と指定時刻を保持する。
使われ方：一般対象宇宙の係数比較と既存版との一致。 -/
lemma dgWalkingHomPrecomposeDirect_coefficient_naturality {p q : D} (y : D)
    (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q)
    {n : ℕ} (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D q y).obj (Opposite.op ⟨n⟩))
    (β : Fin (n + 2) →o Fin 2) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPrecomposeNatTransDirect A D y r).simplex
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPinched A D q y).app _ s).val β).map Q =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPrecomposeNatTransDirect A E (Q.obj y) (Q.onClosed.map r)).simplex
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPinched A E (Q.obj q) (Q.obj y)).app _
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (Q.map q y)).app _ s)).val β := by
  have hc := congrArg (fun f => (f.app (Opposite.op ⟨n⟩) s).val)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomMap_pinched A (Q.map q y))
  have hv := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorPinchedChainMap_val A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomMap A (Q.map q y))
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPinched A D q y).app _ s)).symm.trans hc
  exact (dgWalkingHomPrecomposeDirect_simplex_naturality A D E Q y r _ β).trans
    (congrArg (fun t =>
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPrecomposeNatTransDirect A E (Q.obj y) (Q.onClosed.map r)).simplex t β) hv)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
