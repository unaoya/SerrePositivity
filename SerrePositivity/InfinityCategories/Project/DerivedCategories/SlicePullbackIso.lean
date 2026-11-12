module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SlicePullbackFamilies
/-!
概要：引き戻し内の slice と、整合する二成分の slice の引き戻しを厳密に同定する。
方針：全錐の復元と両成分の等式を使い、標準比較の両逆則を確認する。
規約：標的の充填性を要求しない。使われ方：右 Kan 比較の slice の厳密な基底変換表示。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits SSet
variable {K E F B A A' : SSet.{u}} (f : E ⟶ B) (g : F ⟶ B) (a : K ⟶ pullback f g)
/-- 全錐の復元は、任意パラメータ変更と厳密に可換。 -/
lemma slicePullbackBackwardFamily_naturality (v : A' ⟶ A)
    (s : A ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.slicePullbackDiagram f g a) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.slicePullbackBackwardFamily f g a (v ≫ s) = v ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.slicePullbackBackwardFamily f g a s := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_injective a
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.slicePullbackBackwardFamily f g a s) v,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.slicePullbackBackwardFamily_uncurry, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.slicePullbackBackwardFamily_uncurry]
  apply pullback.hom_ext
  · rw [pullback.lift_fst,
      Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap v (𝟙 K)) _ (pullback.fst f g), pullback.lift_fst]
    simpa only [Category.assoc] using! _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp (s ≫ pullback.fst _ _) v
  · rw [pullback.lift_snd,
      Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap v (𝟙 K)) _ (pullback.snd f g), pullback.lift_snd]
    simpa only [Category.assoc] using! _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp (s ≫ pullback.snd _ _) v
/-- 全錐を二成分へ写して復元すると、元の全錐そのもの。 -/
lemma slicePullbackFamily_backward_forward (s : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.slicePullbackBackwardFamily f g a (s ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.slicePullbackMap f g a) = s := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_injective a
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.slicePullbackBackwardFamily_uncurry]
  apply pullback.hom_ext
  · rw [pullback.lift_fst]
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.slicePullbackMap, pullback.lift_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_postcomp]
  · rw [pullback.lift_snd]
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.slicePullbackMap, pullback.lift_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_postcomp]
/-- 二成分の全錐を復元して射影すると、元の同じ二成分の全錐へ戻る。 -/
lemma slicePullbackFamily_forward_backward (s : A ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.slicePullbackDiagram f g a) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.slicePullbackBackwardFamily f g a s ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.slicePullbackMap f g a = s := by
  apply pullback.hom_ext
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.slicePullbackMap, pullback.lift_fst, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.slicePullbackBackwardFamily_fst]
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.slicePullbackMap, pullback.lift_snd, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.slicePullbackBackwardFamily_snd]
/-- 引き戻し内の slice と、整合する二成分の全 slice の厳密同型。 -/
def slicePullbackIso : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a ≅ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.slicePullbackDiagram f g a where
  hom := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.slicePullbackMap f g a
  inv := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.slicePullbackBackwardFamily f g a (𝟙 _)
  hom_inv_id := by
    rw [← slicePullbackBackwardFamily_naturality, Category.comp_id]
    exact slicePullbackFamily_backward_forward f g a (𝟙 _)
  inv_hom_id := slicePullbackFamily_forward_backward f g a (𝟙 _)
/-- 引き戻し内の全錐は、二成分の全錐で厳密に検出できる。 -/
lemma slicePullbackPostcomp_jointly_monic {s t : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a}
    (hE : s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp a (pullback.fst f g) =
      t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp a (pullback.fst f g))
    (hF : s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp a (pullback.snd f g) =
      t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp a (pullback.snd f g)) : s = t := by
  have h : s ≫ (slicePullbackIso f g a).hom = t ≫ (slicePullbackIso f g a).hom := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, slicePullbackIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.slicePullbackMap, pullback.lift_fst] using hE
    · simpa only [Category.assoc, slicePullbackIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.slicePullbackMap, pullback.lift_snd] using hF
  exact (cancel_mono (slicePullbackIso f g a).hom).mp h
end SerrePositivity.InfinityCategories.Project.DerivedCategories
