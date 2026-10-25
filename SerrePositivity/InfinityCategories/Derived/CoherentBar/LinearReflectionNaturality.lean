module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.LinearReflectionData
public import SerrePositivity.InfinityCategories.Derived.DGNerveOppositeReindex
public import SerrePositivity.InfinityCategories.Derived.PinchedLinearChainMap
/-!
概要：線形座標の反転は、反転した全添字写像と厳密に可換である。
方針：部分集合上の単射分岐では反転像、非単射分岐では零成分を比較する。
規約：面・退化に加えて任意の単調写像を含む。
使われ方：左右 pinched Hom 比較を実単体写像として組み立てる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom DGNerveOppositeIndex
variable {R : Type u} [CommRing R] {C : Type v} [DGCategory R C] {x y : C}

private lemma component_eq_of_set_eq {n : ℕ} (f : LinearData R x y n)
    {J K : Finset (Fin (n + 1))} {k : ℤ} {hJ : J.Nonempty} {hK : K.Nonempty}
    {hkJ : k = 1 - (J.card : ℤ)} {hkK : k = 1 - (K.card : ℤ)} (h : J = K) :
    f.component J k hJ hkJ = f.component K k hK hkK := by
  cases h
  rfl

lemma dgCoherentBarLinearReflectionData_pullback {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (f : LinearData R x y n) :
    dgCoherentBarLinearReflectionData (LinearData.pullback (reverseOrderHom α) f) =
      LinearData.pullback α (dgCoherentBarLinearReflectionData f) := by
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change (dgCoherentBarLinearReflectionData
    (LinearData.pullback (reverseOrderHom α) f)).component J k hJ hk =
      (LinearData.pullback α (dgCoherentBarLinearReflectionData f)).component J k hJ hk
  rw [dgCoherentBarLinearReflectionData_component]
  by_cases hi : Set.InjOn α (J : Set (Fin (m + 1)))
  · have hiRev : Set.InjOn (reverseOrderHom α) (reverse J : Set (Fin (m + 1))) := by
      apply (reverseOrderHom_injOn_iff α (reverse J)).mpr
      simpa only [reverse_reverse] using hi
    rw [LinearData.pullback_component_of_inj _ _ _ _ _ _ hiRev,
      LinearData.pullback_component_of_inj _ _ _ _ _ _ hi,
      dgCoherentBarLinearReflectionData_component,
      Finset.card_image_of_injOn hi]
    congr 1
    exact component_eq_of_set_eq f (reverse_image α J).symm
  · have hiRev : ¬ Set.InjOn (reverseOrderHom α) (reverse J : Set (Fin (m + 1))) := by
      intro h
      apply hi
      simpa only [reverse_reverse] using
        (reverseOrderHom_injOn_iff α (reverse J)).mp h
    rw [LinearData.pullback_component_of_not_inj _ _ _ _ _ _ hiRev,
      LinearData.pullback_component_of_not_inj _ _ _ _ _ _ hi, smul_zero]

lemma dgCoherentBarLinearReflectionSimplex_involution {n : ℕ} (f : LinearSimplex R x y n) :
    dgCoherentBarLinearReflectionSimplex (dgCoherentBarLinearReflectionSimplex f) = f := by
  apply Subtype.ext
  exact dgCoherentBarLinearReflectionData_involution f.val

lemma dgCoherentBarLinearReflectionSimplex_pullback {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (f : LinearSimplex R x y n) :
    dgCoherentBarLinearReflectionSimplex (LinearSimplex.pullback (reverseOrderHom α) f) =
      LinearSimplex.pullback α (dgCoherentBarLinearReflectionSimplex f) := by
  apply Subtype.ext
  exact dgCoherentBarLinearReflectionData_pullback α f.val

end SerrePositivity.InfinityCategories
