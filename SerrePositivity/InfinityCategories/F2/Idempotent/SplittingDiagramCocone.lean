module

public import SerrePositivity.InfinityCategories.F2.Idempotent.WalkingFullCoconePoint
public import SerrePositivity.InfinityCategories.F2.Idempotent.IdemCoconeRestriction
public import SerrePositivity.InfinityCategories.HomotopyLimits.NerveOpposite
public import SerrePositivity.InfinityCategories.Stable.IdentityCocone

/-!
概要：任意の quasicategory への元の強分裂図式の全余錐は、余極限余錐である。
方針：元の終対象の一点への right anodyne 制限後を、同じ定値な一点余錐と照合する。
規約：元の全図式と元の全余錐を保持し、標的の関手に余極限保存を仮定しない。
使われ方：HTT 4.4.5.12 の元の Idem 余錐の普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の強分裂図式の、同じ全分裂頂点への元の全余錐。 -/
def splittingDiagramCocone {X : SSet.{u}} (F : SplitShape ⟶ X) : JoinCocone F :=
  ⟨walkingFullJoinCocone.val ≫ F, by
    rw [← Category.assoc, walkingFullJoinCocone.property, Category.id_comp]⟩

/-- 元の終対象の一点への制限は、元の分裂頂点への定値な全余錐。 -/
lemma splittingDiagramCocone_point {X : SSet.{u}} (F : SplitShape ⟶ X) :
    ((splittingDiagramCocone F).restrict (nervePoint walkingImage)).val =
      SSet.const (F.app (Opposite.op ⦋0⦌) (nerveVertex walkingImage)) := by
  change joinMap (nervePoint walkingImage) (𝟙 (Δ[0] : SSet.{u})) ≫
    (walkingFullJoinCocone.val ≫ F) = _
  rw [← Category.assoc, walkingFullJoinCocone_point_restrict, SSet.const_comp]

/-- 元の終対象の元の一点包含は right anodyne。 -/
lemma walkingImagePoint_rightAnodyne : rightAnodyneExtensions (nervePoint walkingImage.{u}) :=
  HomotopyLimits.nervePoint_terminal_rightAnodyne walkingImage_isTerminal

/-- 任意の quasicategory 内の元の全強分裂図式の指定余錐は、余極限余錐。 -/
lemma splittingDiagramCocone_isColimit {X : SSet.{u}} [Quasicategory X]
    (F : SplitShape ⟶ X) : IsColimitCone (splittingDiagramCocone F) := by
  have : Mono (nervePoint walkingImage.{u}) := cofinalPointInclusion_mono (nerveVertex walkingImage)
  apply (isColimitCone_iff_restrict_of_rightAnodyne (splittingDiagramCocone F)
    (nervePoint walkingImage) walkingImagePoint_rightAnodyne).mpr
  exact isColimitCone_of_point_constant _ _ (splittingDiagramCocone_point F)

end SerrePositivity.InfinityCategories.F2.Idempotent
