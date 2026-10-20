module

public import SerrePositivity.InfinityCategories.F2.ConstantPullbackCoordinates
public import SerrePositivity.InfinityCategories.F2.ConstantDiagramTransformation
public import SerrePositivity.InfinityCategories.F1.UnstraighteningFamilyWitness
public import SerrePositivity.InfinityCategories.F1.FiberTransportFamily

/-!
概要：定値図式間の変換の pointed な証拠を、元の区間の族の fiber 輸送として表示する。
方針：元の prism の二端と底を、定値引き戻しの座標で読み直す。
規約：元の証拠と区間の全パラメータを保つ。
使われ方：定値 unstraightening の作用を底に依存しない普遍輸送と比較する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：定値 unstraightening の元の fiber 座標への射影。
方針：直積表示の第一射影を取る。規約：元の比較を保持。使われ方：輸送の始点。 -/
def constantUnstraighteningFiberProjection (B : SSet.{u + 1}) (x : SpaceInfinity.{u} _⦋0⦌) :
    leftUnstraightening (SSet.const x : B ⟶ SpaceInfinity) ⟶
      vertexFiber pointedSpaceProjection x :=
  (constantPullbackFiberIso pointedSpaceProjection x).hom ≫ fst _ B

/-- 概要：定値図式の変換の指定証拠は、同じ区間の全族の pointed-space 輸送族。
方針：元の prism をそのまま使い、二端を fiber に、底を元の区間に同定する。
規約：元の prism を変更しない。使われ方：定値標的の作用の選択独立性。 -/
def constantDiagramTransportWitness {B T : SSet.{u + 1}}
    {x y : SpaceInfinity.{u} _⦋0⦌} {a : T ⟶ intervalMappingSpace x y}
    {g : leftUnstraightening (SSet.const x : B ⟶ _) ⊗ T ⟶
      leftUnstraightening (SSet.const y : B ⟶ _)}
    (w : UnstraighteningFamilyWitness (SSet.const x) (SSet.const y)
      (constantDiagramTransformation B a) g) :
    FiberTransportFamily (b := y) pointedSpaceProjection
      (constantUnstraighteningFiberProjection B x) (intervalMappingUncurry a) where
  endpoint := vertexFiberLift pointedSpaceProjection y
    (g ≫ pullback.fst pointedSpaceProjection (SSet.const y : B ⟶ _)) (by
      rw [Category.assoc, pullback.condition, SSet.comp_const, SSet.comp_const])
  prism := w.leftPrism
  start := by
    rw [UnstraighteningFamilyWitness.leftPrism, ← Category.assoc,
      prismEndpoint_associator_inv, w.source]
    simp only [constantUnstraighteningFiberProjection, Category.assoc,
      constantPullbackFiberIso_fst_ι]
  finish := by
    rw [UnstraighteningFamilyWitness.leftPrism, ← Category.assoc,
      prismEndpoint_associator_inv, w.target, vertexFiberLift_ι]
  over_base := by
    rw [w.leftPrism_projection, constantDiagramTransformation_diagram]
    rfl

end SerrePositivity.InfinityCategories.F2
