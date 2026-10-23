module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ConstantDiagramTransportWitness

/-!
概要：元の定値図式の pointed 輸送証拠の終点を、元の作用と同じ fiber 射影で読む。
方針：fiber の包含後に元の第一射影と vertexFiberLift の評価式を使う。
規約：元の証拠を保持。使われ方：長辺の実輸送を元の全空間の合成射へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の定値 unstraightening の fiber 座標を含めると、元の第一射影を回収する。 -/
lemma constantUnstraighteningFiberProjection_ι (B : SSet.{u + 1})
    (z : SpaceInfinity.{u} _⦋0⦌) :
    constantUnstraighteningFiberProjection B z ≫ vertexFiberι pointedSpaceProjection z =
      pullback.fst pointedSpaceProjection (SSet.const z : B ⟶ SpaceInfinity) := by
  unfold constantUnstraighteningFiberProjection
  exact (Category.assoc _ _ _).trans (constantPullbackFiberIso_fst_ι pointedSpaceProjection z)

/-- 元の指定証拠の輸送終点は、同じ全空間の作用の元の fiber 射影そのもの。 -/
lemma constantDiagramTransportWitness_endpoint {B T : SSet.{u + 1}}
    {x y : SpaceInfinity.{u} _⦋0⦌} {a : T ⟶ intervalMappingSpace x y}
    {g : leftUnstraightening (SSet.const x : B ⟶ _) ⊗ T ⟶
      leftUnstraightening (SSet.const y : B ⟶ _)}
    (w : UnstraighteningFamilyWitness (SSet.const x) (SSet.const y)
      (constantDiagramTransformation B a) g) :
    (constantDiagramTransportWitness w).endpoint =
      g ≫ constantUnstraighteningFiberProjection B y := by
  apply vertexFiber_hom_ext pointedSpaceProjection y
  dsimp only [constantDiagramTransportWitness]
  rw [vertexFiberLift_ι, Category.assoc, constantUnstraighteningFiberProjection_ι]

end SerrePositivity.InfinityCategories.F2
