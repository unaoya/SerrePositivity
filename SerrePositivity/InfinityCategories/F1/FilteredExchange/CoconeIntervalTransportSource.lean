module

public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Categories.PointedSpaces
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.CoconeFiberEvaluation
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ConstantDiagramTransportWitness
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ConstantPullbackFiber

/-!
概要：元の余錐単位の二座標を、全区間輸送の比較の同じ始点射として保持する。
方針：元の fiber 写像と底への射影を同じ定値引き戻し同型で束ねる。
規約：単位を選び直さない。使われ方：下側輸送因子の値と全三角形の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u + 1}} {F : B ⟶ SpaceInfinity.{u}} (c : JoinCocone F)
  (T : SSet.{u + 1})
local notation "E" => leftUnstraightening F

/-- 元の余錐単位の二座標に、同じ全区間係数を添えた実際の射。 -/
def coconeIntervalTransportSource : E ⊗ T ⟶
    leftUnstraightening (SSet.const c.vertex : B ⟶ SpaceInfinity) ⊗ T :=
  lift (lift (fst E T ≫ coconeFiberMap c) (fst E T ≫ leftUnstraighteningProjection F) ≫
    (constantPullbackFiberIso pointedSpaceProjection c.vertex).inv) (snd E T)

/-- 元の二座標の射を fiber へ射影すると、同じ余錐 fiber 写像と全係数を回収する。 -/
lemma coconeIntervalTransportSource_projection :
    coconeIntervalTransportSource c T ≫ (constantUnstraighteningFiberProjection B c.vertex ▷ T) =
      lift (fst E T ≫ coconeFiberMap c) (snd E T) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, whiskerRight_fst, ← Category.assoc, lift_fst]
    dsimp only [coconeIntervalTransportSource, constantUnstraighteningFiberProjection]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, lift_fst]
  · rw [Category.assoc, whiskerRight_snd, lift_snd]
    rfl

end SerrePositivity.InfinityCategories.F2
