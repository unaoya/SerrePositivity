module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.ConstantDiagramTransportCoordinates
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FiberTransportFamilyRightPrism
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FiberTransportFamilyRightComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ConstantDiagramTransportComparison

/-!
概要：定値図式の実輸送の右結合表示から、元の指定 prism を厳密に回収する。
方針：結合子を消去し、普遍証拠の制限と始域恒等射の二表示を比較する。
規約：指定された証拠を保持。使われ方：元の三角形比較の輸送因子の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の証拠から構成した輸送の右結合 prism は、同じ元の prism そのもの。 -/
lemma constantDiagramTransportWitness_rightPrism {B T : SSet.{u + 1}}
    {x y : SpaceInfinity.{u} _⦋0⦌} {a : T ⟶ intervalMappingSpace x y}
    {g : leftUnstraightening (SSet.const x : B ⟶ _) ⊗ T ⟶
      leftUnstraightening (SSet.const y : B ⟶ _)}
    (w : UnstraighteningFamilyWitness (SSet.const x) (SSet.const y)
      (constantDiagramTransformation B a) g) :
    fiberTransportFamilyRightPrism (constantDiagramTransportWitness w) = w.prism := by
  simp only [fiberTransportFamilyRightPrism, constantDiagramTransportWitness,
    UnstraighteningFamilyWitness.leftPrism, Iso.hom_inv_id_assoc]

/-- 元の定値図式の prism の底は、同じ輸送の右結合した底と厳密に一致。 -/
lemma constantDiagramTransportWitness_rightBase {B T : SSet.{u + 1}}
    {x y : SpaceInfinity.{u} _⦋0⦌} {a : T ⟶ intervalMappingSpace x y}
    {g : leftUnstraightening (SSet.const x : B ⟶ _) ⊗ T ⟶
      leftUnstraightening (SSet.const y : B ⟶ _)}
    (w : UnstraighteningFamilyWitness (SSet.const x) (SSet.const y)
      (constantDiagramTransformation B a) g) :
    ((Δ[1] ◁ leftUnstraighteningProjection (SSet.const x : B ⟶ _)) ▷ T) ≫
        functorParameterizedPrism (intervalMappingUncurry (constantDiagramTransformation B a)) =
      fiberTransportFamilyRightBase (leftUnstraightening (SSet.const x : B ⟶ _))
        (intervalMappingUncurry a) := by
  refine w.projection.symm.trans ?_
  rw [← constantDiagramTransportWitness_rightPrism w]
  exact fiberTransportFamilyRightPrism_projection (constantDiagramTransportWitness w)

/-- 定値図式の普遍証拠は、始域恒等射付き比較が使う同じ普遍 prism。 -/
lemma constantDiagramMappingFamilyWitness_prism {T : SSet.{u + 1}}
    (B : SSet.{u + 1}) {x y : SpaceInfinity.{u} _⦋0⦌}
    (a : T ⟶ intervalMappingSpace x y) :
    (constantDiagramMappingFamilyWitness B a).prism =
      ((Δ[1] ◁ 𝟙 (leftUnstraightening (SSet.const x : B ⟶ _))) ⊗ₘ
        constantDiagramTransformation B a) ≫
      leftUnstraighteningTransformationFamilyLift (SSet.const x : B ⟶ _) (SSet.const y) := by
  apply SSet.hom_ext
  intro n
  rfl

end SerrePositivity.InfinityCategories.F2
