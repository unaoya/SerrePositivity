module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCenterSpanShapeMaps

/-!
概要：中央の実三点 span と標準ホーンの厳密同型。
方針：同じ実図式の native 余錐と頂点を保持して比較する。
規約：一般安定性を先取りしない。使われ方：HA 1.4.2.15 の中央面。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
variable {P : Type u} [PartialOrder P]

def excisionGridCenterSpanPastingIso : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCenterSpanIndex.{u} ≅
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpan : SSet.{u}) where
  hom := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCenterSpanToPasting
  inv := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridPastingToCenterSpan
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply CategoryTheory.nerve.ext_of_isThin
    funext k
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply ULift.ext
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · rfl
    · change (s.obj k).val.val.val.val.down.val.2.val - 1 + 1 =
        (s.obj k).val.val.val.val.down.val.2.val
      have := (s.obj k).property.2
      change 1 ≤ (s.obj k).val.val.val.val.down.val.2.val at this
      omega
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext <;> apply stdSimplex.ext <;> intro k
    · rfl
    · apply Fin.ext
      change ((stdSimplex.objEquiv s.val.val.2).toOrderHom k).val + 1 - 1 =
        ((stdSimplex.objEquiv s.val.val.2).toOrderHom k).val
      omega

def excisionGridCenterSpanShapeIso : (horn 2 0 : SSet.{u}) ≅
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridPastIndex.{u})
      (fun v ↦ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridCenterSpan (nerveEquiv v)) : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpanIso ≪≫ excisionGridCenterSpanPastingIso.symm ≪≫
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeNerveIso _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridCenterSpan

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
