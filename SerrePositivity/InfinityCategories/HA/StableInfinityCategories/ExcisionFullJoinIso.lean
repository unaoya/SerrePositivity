module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.InitialJoinIso
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreCospanBoundary
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCorePunctured
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullInitialFunctors
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullInitialInverse
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullPuncturedIndex
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridInitialPoint
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionSquareGrid
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetInteriorPrism
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PullbackConeVertex
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ThinNerveConeComparison
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ThinNerveMonomorphism

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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

def excisionFullInitialNerveIso :
    nerve (WithInitial _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullPuncturedIndex.{u}) ≅ nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} := by
  have := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionFullWithInitial_isThin.{u}
  exact {
    hom := nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionWithInitialToFull
    inv := nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionFullToWithInitial
    hom_inv_id := by
      apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
      intro v
      exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionFullToWithInitial_after_inverse (nerveEquiv v)
    inv_hom_id := by
      apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
      intro v
      exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionWithInitialToFull_after_inverse (nerveEquiv v) }

def excisionFullJoinIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) (nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullPuncturedIndex.{u}) ≅
      nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinNerveIso _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullPuncturedIndex ≪≫ excisionFullInitialNerveIso

lemma excisionFullJoinIso_inr :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) (nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullPuncturedIndex.{u}) ≫
      excisionFullJoinIso.hom = nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionFullPunctured) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] (nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullPuncturedIndex) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinNerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullPuncturedIndex ≫
      nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionWithInitialToFull) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_initialJoinNerveMap]
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
  intro v
  rfl

lemma excisionFullJoinIso_inl :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullPuncturedIndex.{u}) ≫
      excisionFullJoinIso.hom = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridInitialPoint := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] (nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullPuncturedIndex) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinNerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullPuncturedIndex ≫
      nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionWithInitialToFull) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_initialJoinNerveMap]
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
  intro v
  rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
