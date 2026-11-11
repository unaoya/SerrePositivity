module

public import SerrePositivity.AlgebraicGeometry.SectionComponentAgreement
public import Mathlib.Topology.NoetherianSpace

/-!
概要：有限局所自由な標識の自己ファイバー積で切断が同じ成分を選ぶとき、その開部分を降下する。
方針：閉写像で基底を縮め、二つの逆像が一致する開部分を開写像の像として降ろす。
規約：二つの切断の成分の集合は、自己ファイバー積の二つの射による逆像とする。
使われ方：滑らかな族の幾何学的整な成分の広がり。
-/

@[expose] public section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Limits TopologicalSpace

/--
概要：自己ファイバー積の二つの切断が指定ファイバー上で同じ成分を選ぶなら、
基底を縮めて標識上の成分の開部分を降下できる。
方針：閉写像で一致を近傍まで広げ、開写像の像が元の開部分を回収することを確かめる。
規約：自己ファイバー積の図式と切断の成分との比較は仮定で与える。
使われ方：Stacks 057I の有限局所自由な標識を使う降下。
-/
theorem exists_open_sectionComponentMarker_descent
    {P Z X Q S : Scheme.{u}} [NoetherianSpace Z]
    {i : Z ⟶ X} {u v : P ⟶ Z} (hPb : IsPullback u v i i) (hi : IsOpenMap i)
    (f : X ⟶ S) (p : P ⟶ Q) (q : Q ⟶ S) (hq : IsClosedMap q)
    (hbase : u ≫ i ≫ f = p ≫ q)
    (W : Z.Opens) (s t : Q ⟶ P) (hs : s ≫ p = 𝟙 Q)
    (hu : u ⁻¹' (W : Set Z) = sectionComponentLocus p s)
    (hv : v ⁻¹' (W : Set Z) = sectionComponentLocus p t)
    (a : S) (h : ∀ y : Q, q y = a → s y ∈ sectionComponentLocus p t) :
    ∃ (U : S.Opens) (V : X.Opens), IsAffineOpen U ∧ a ∈ U ∧ IsCompact (V : Set X) ∧
      V ≤ f ⁻¹ᵁ U ∧ i ⁻¹' (V : Set X) = (W : Set Z) ∩ (i ≫ f) ⁻¹' (U : Set S) := by
  have ht : IsOpen (sectionComponentLocus p t) := hv ▸ W.isOpen.preimage v.continuous
  obtain ⟨U, hU, ha, heq⟩ :=
    exists_affine_open_sectionComponentLoci_agree_of_isClosedMap p s t q hs hq ht a h
  let W₀ : Z.Opens := W ⊓ (i ≫ f) ⁻¹ᵁ U
  let V : X.Opens := ⟨i '' (W₀ : Set Z), hi _ W₀.isOpen⟩
  have hpre : u ⁻¹' (W₀ : Set Z) = v ⁻¹' (W₀ : Set Z) := by
    change u ⁻¹' ((W : Set Z) ∩ (i ≫ f) ⁻¹' (U : Set S)) =
      v ⁻¹' ((W : Set Z) ∩ (i ≫ f) ⁻¹' (U : Set S))
    have hbase' : v ≫ i ≫ f = p ≫ q := by rw [← Category.assoc, ← hPb.w, Category.assoc, hbase]
    rw [Set.preimage_inter, Set.preimage_inter, hu, hv,
      ← Set.preimage_comp, ← Set.preimage_comp]
    change sectionComponentLocus p s ∩ (u ≫ i ≫ f) ⁻¹' (U : Set S) =
      sectionComponentLocus p t ∩ (v ≫ i ≫ f) ⁻¹' (U : Set S)
    rw [hbase, hbase', heq]
  refine ⟨U, V, hU, ha, (NoetherianSpace.isCompact (W₀ : Set Z)).image i.continuous, ?_, ?_⟩
  · rintro x ⟨z, hz, rfl⟩
    exact hz.2
  · change i ⁻¹' (i '' (W₀ : Set Z)) = (W₀ : Set Z)
    refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
    rw [← Scheme.image_preimage_eq_of_isPullback hPb, hpre]
    exact Set.image_preimage_subset _ _

end SerrePositivity.AlgebraicGeometry
