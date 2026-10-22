module
public import SerrePositivity.InfinityCategories.Stable.ExcisionFullInitialInverse
public import SerrePositivity.InfinityCategories.Stable.PosetInteriorPrism
public import SerrePositivity.InfinityCategories.Stable.ExcisionCorePunctured
public import SerrePositivity.InfinityCategories.Stable.ThinNerveMonomorphism
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialJoinIso
public import SerrePositivity.InfinityCategories.Stable.ThinNerveConeComparison
public import SerrePositivity.InfinityCategories.Stable.PullbackConeVertex
public import SerrePositivity.InfinityCategories.F2.ConeValEquality
public import SerrePositivity.InfinityCategories.Stable.ExcisionSquareGrid
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreCospanBoundary

/-!
概要：比較格子の初期角を実引き戻しへ置換し、矢印圏の普遍性へ接続する。
方針：穿孔格子の同じ錐と全非初期単体を厳密に保持する。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の第二条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

def excisionFullInitialNerveIso :
    nerve (WithInitial ExcisionFullPuncturedIndex.{u}) ≅ nerve ExcisionGridIndex.{u} := by
  have := excisionFullWithInitial_isThin.{u}
  exact {
    hom := nerveMap excisionWithInitialToFull
    inv := nerveMap excisionFullToWithInitial
    hom_inv_id := by
      apply thinNerveHom_ext_of_vertices
      intro v
      exact excisionFullToWithInitial_after_inverse (nerveEquiv v)
    inv_hom_id := by
      apply thinNerveHom_ext_of_vertices
      intro v
      exact excisionWithInitialToFull_after_inverse (nerveEquiv v) }

def excisionFullJoinIso :
    join (Δ[0] : SSet.{u}) (nerve ExcisionFullPuncturedIndex.{u}) ≅
      nerve ExcisionGridIndex.{u} :=
  HomotopyLimits.initialJoinNerveIso ExcisionFullPuncturedIndex ≪≫ excisionFullInitialNerveIso

lemma excisionFullJoinIso_inr :
    joinInr (Δ[0] : SSet.{u}) (nerve ExcisionFullPuncturedIndex.{u}) ≫
      excisionFullJoinIso.hom = nerveMap (posetSubtypeInclusion IsExcisionFullPunctured) := by
  change joinInr Δ[0] (nerve ExcisionFullPuncturedIndex) ≫
    (HomotopyLimits.initialJoinNerveMap ExcisionFullPuncturedIndex ≫
      nerveMap excisionWithInitialToFull) = _
  rw [← Category.assoc, HomotopyLimits.joinInr_initialJoinNerveMap]
  apply thinNerveHom_ext_of_vertices
  intro v
  rfl

lemma excisionFullJoinIso_inl :
    joinInl (Δ[0] : SSet.{u}) (nerve ExcisionFullPuncturedIndex.{u}) ≫
      excisionFullJoinIso.hom = nervePoint excisionGridInitialPoint := by
  change joinInl Δ[0] (nerve ExcisionFullPuncturedIndex) ≫
    (HomotopyLimits.initialJoinNerveMap ExcisionFullPuncturedIndex ≫
      nerveMap excisionWithInitialToFull) = _
  rw [← Category.assoc, HomotopyLimits.joinInl_initialJoinNerveMap]
  apply thinNerveHom_ext_of_vertices
  intro v
  rfl

end SerrePositivity.InfinityCategories
