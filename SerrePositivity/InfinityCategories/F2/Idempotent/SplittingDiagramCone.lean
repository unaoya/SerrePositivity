module

public import SerrePositivity.InfinityCategories.F2.Idempotent.WalkingFullConePoint
public import SerrePositivity.InfinityCategories.F2.Idempotent.IdemConeRestriction
public import SerrePositivity.InfinityCategories.F2.Idempotent.PointConeLimit

/-!
概要：任意の quasicategory への元の強分裂図式の全錐は、極限錐である。
方針：元の始対象の一点への left anodyne 制限後を、同じ定値な一点錐と照合する。
規約：元の全図式と元の全錐を保持し、標的の関手に極限保存を仮定しない。
使われ方：HTT 4.4.5.13 の元の Idem 錐の普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の強分裂図式の、同じ全分裂頂点からの元の全錐。 -/
def splittingDiagramCone {X : SSet.{u}} (F : SplitShape ⟶ X) : JoinCone F :=
  ⟨walkingFullJoinCone.val ≫ F, by
    rw [← Category.assoc, walkingFullJoinCone.property, Category.id_comp]⟩

/-- 元の始対象の一点への制限は、元の分裂頂点への定値な全錐。 -/
lemma splittingDiagramCone_point {X : SSet.{u}} (F : SplitShape ⟶ X) :
    (F2.restrictJoinCone (splittingDiagramCone F) (nervePoint walkingImage)).val =
      SSet.const (F.app (Opposite.op ⦋0⦌) (nerveVertex walkingImage)) := by
  change joinMap (𝟙 (Δ[0] : SSet.{u})) (nervePoint walkingImage) ≫
    (walkingFullJoinCone.val ≫ F) = _
  rw [← Category.assoc, walkingFullJoinCone_point_restrict, SSet.const_comp]

/-- 元の始対象の元の一点包含は left anodyne。 -/
lemma walkingImagePoint_leftAnodyne : leftAnodyneExtensions (nervePoint walkingImage.{u}) :=
  nervePoint_leftAnodyne walkingImage_isInitial

/-- 任意の quasicategory 内の元の全強分裂図式の指定錐は、極限錐。 -/
lemma splittingDiagramCone_isLimit {X : SSet.{u}} [Quasicategory X]
    (F : SplitShape ⟶ X) : IsLimitCone (splittingDiagramCone F) := by
  have := sliceOverRestrict_trivialKanFibration F
    (nervePoint walkingImage) walkingImagePoint_leftAnodyne
  apply ((qCatEquivalenceOfTrivialKanFibration
    (sliceOverRestrict F (nervePoint walkingImage))).isTerminalVertex_iff
      (splittingDiagramCone F)).mpr
  exact pointCone_isLimit_of_constant _ _ (splittingDiagramCone_point F)

end SerrePositivity.InfinityCategories.F2.Idempotent
