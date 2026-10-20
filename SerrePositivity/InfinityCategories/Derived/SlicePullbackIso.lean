module
public import SerrePositivity.InfinityCategories.Derived.SlicePullbackFamilies
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits SSet
variable {K E F B A A' : SSet.{u}} (f : E ⟶ B) (g : F ⟶ B) (a : K ⟶ pullback f g)
/-- 全錐の復元は、任意パラメータ変更と厳密に可換。 -/
lemma slicePullbackBackwardFamily_naturality (v : A' ⟶ A)
    (s : A ⟶ slicePullbackDiagram f g a) :
    slicePullbackBackwardFamily f g a (v ≫ s) = v ≫ slicePullbackBackwardFamily f g a s := by
  apply sliceOverUncurry_injective a
  rw [sliceOverUncurry_precomp (slicePullbackBackwardFamily f g a s) v,
    slicePullbackBackwardFamily_uncurry, slicePullbackBackwardFamily_uncurry]
  apply pullback.hom_ext
  · rw [pullback.lift_fst,
      Category.assoc (joinMap v (𝟙 K)) _ (pullback.fst f g), pullback.lift_fst]
    simpa only [Category.assoc] using! sliceOverUncurry_precomp (s ≫ pullback.fst _ _) v
  · rw [pullback.lift_snd,
      Category.assoc (joinMap v (𝟙 K)) _ (pullback.snd f g), pullback.lift_snd]
    simpa only [Category.assoc] using! sliceOverUncurry_precomp (s ≫ pullback.snd _ _) v
/-- 全錐を二成分へ写して復元すると、元の全錐そのもの。 -/
lemma slicePullbackFamily_backward_forward (s : A ⟶ sliceOver a) :
    slicePullbackBackwardFamily f g a (s ≫ slicePullbackMap f g a) = s := by
  apply sliceOverUncurry_injective a
  rw [slicePullbackBackwardFamily_uncurry]
  apply pullback.hom_ext
  · rw [pullback.lift_fst]
    rw [Category.assoc, slicePullbackMap, pullback.lift_fst, sliceOverUncurry_postcomp]
  · rw [pullback.lift_snd]
    rw [Category.assoc, slicePullbackMap, pullback.lift_snd, sliceOverUncurry_postcomp]
/-- 二成分の全錐を復元して射影すると、元の同じ二成分の全錐へ戻る。 -/
lemma slicePullbackFamily_forward_backward (s : A ⟶ slicePullbackDiagram f g a) :
    slicePullbackBackwardFamily f g a s ≫ slicePullbackMap f g a = s := by
  apply pullback.hom_ext
  · rw [Category.assoc, slicePullbackMap, pullback.lift_fst, slicePullbackBackwardFamily_fst]
  · rw [Category.assoc, slicePullbackMap, pullback.lift_snd, slicePullbackBackwardFamily_snd]
/-- 引き戻し内の slice と、整合する二成分の全 slice の厳密同型。 -/
def slicePullbackIso : sliceOver a ≅ slicePullbackDiagram f g a where
  hom := slicePullbackMap f g a
  inv := slicePullbackBackwardFamily f g a (𝟙 _)
  hom_inv_id := by
    rw [← slicePullbackBackwardFamily_naturality, Category.comp_id]
    exact slicePullbackFamily_backward_forward f g a (𝟙 _)
  inv_hom_id := slicePullbackFamily_forward_backward f g a (𝟙 _)
/-- 引き戻し内の全錐は、二成分の全錐で厳密に検出できる。 -/
lemma slicePullbackPostcomp_jointly_monic {s t : A ⟶ sliceOver a}
    (hE : s ≫ sliceOverPostcomp a (pullback.fst f g) =
      t ≫ sliceOverPostcomp a (pullback.fst f g))
    (hF : s ≫ sliceOverPostcomp a (pullback.snd f g) =
      t ≫ sliceOverPostcomp a (pullback.snd f g)) : s = t := by
  have h : s ≫ (slicePullbackIso f g a).hom = t ≫ (slicePullbackIso f g a).hom := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, slicePullbackIso, slicePullbackMap, pullback.lift_fst] using hE
    · simpa only [Category.assoc, slicePullbackIso, slicePullbackMap, pullback.lift_snd] using hF
  exact (cancel_mono (slicePullbackIso f g a).hom).mp h
end SerrePositivity.InfinityCategories
