module
public import SerrePositivity.KST.SConstruction.FamilyChainCompositeClasses
public import SerrePositivity.KST.SConstruction.EndpointFixedEdgeSquares
public import SerrePositivity.KST.SConstruction.MappingSquareUncurry

/-! # 全合成証人を保つ比較円柱の端点固定二次元比較
概要：同じ全補正列の二つの合成円柱を、両端を全時刻で固定する実二次元円柱で比較する。
方針：元の全合成三角形の式から実比較三角形を構成し、同じ正方形を uncurry する。
規約：全パラメータを保ち、二円柱の零・一面と両端を厳密に回収する。
使われ方：全段 raw 比較の構造適合を保つ合成の選択の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {U E : SSet.{u}} [KanComplex E] {f g : U ⟶ E}
  {c : FamilyHomotopyChain f g} {H K : SSet.Homotopy f g}
  (w : FamilyChainCompositionWitness c H) (v : FamilyChainCompositionWitness c K)

/-- 同じ元の全補正列を合成する二円柱の、内部 Hom の実比較正方形。 -/
def familyChainCompositionComparisonSquare :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom U).obj E :=
  endpointFixedEdgeSquare (familyChainCompositionComparisonTriangle w v)

/-- 二つの元の合成円柱を両面に持つ、元の全パラメータの実二次元比較。 -/
def familyChainCompositionComparison : SSet.Homotopy H.h K.h where
  h := mappingSquareUncurry (familyChainCompositionComparisonSquare w v)
  h₀ := by
    rw [mappingSquareUncurry_zero, familyChainCompositionComparisonSquare,
      endpointFixedEdgeSquare_zero]
    change uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry H.h))) = _
    rw [Equiv.symm_apply_apply, uncurry_curry]
    rfl
  h₁ := by
    rw [mappingSquareUncurry_one, familyChainCompositionComparisonSquare,
      endpointFixedEdgeSquare_one]
    change uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry K.h))) = _
    rw [Equiv.symm_apply_apply, uncurry_curry]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 始点族は元の全パラメータで比較の全時刻を通して厳密に固定する。 -/
lemma familyChainCompositionComparison_source :
    (SSet.ι₀ (X := U) ▷ (Δ[1] : SSet.{u})) ≫
        (familyChainCompositionComparison w v).h = fst U (Δ[1] : SSet.{u}) ≫ f := by
  change _ ≫ mappingSquareUncurry (familyChainCompositionComparisonSquare w v) = _
  rw [mappingSquareUncurry_source, familyChainCompositionComparisonSquare,
    endpointFixedEdgeSquare_vertical_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]

/-- 終点族も元の全パラメータで比較の全時刻を通して厳密に固定する。 -/
lemma familyChainCompositionComparison_target :
    (SSet.ι₁ (X := U) ▷ (Δ[1] : SSet.{u})) ≫
        (familyChainCompositionComparison w v).h = fst U (Δ[1] : SSet.{u}) ≫ g := by
  change _ ≫ mappingSquareUncurry (familyChainCompositionComparisonSquare w v) = _
  rw [mappingSquareUncurry_target, familyChainCompositionComparisonSquare,
    endpointFixedEdgeSquare_vertical_one, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]

end SerrePositivity.KST.SConstruction
