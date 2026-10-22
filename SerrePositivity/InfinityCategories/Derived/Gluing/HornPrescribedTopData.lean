module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HornDeletionEquation
public import SerrePositivity.InfinityCategories.Derived.PinchedRelativeSimplexLifting

/-! 利用可能な全ホーン面と任意の最上位成分を同時に保つ線形データ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve.PinchedHom
open scoped Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D] {x y : D}
  {n : ℕ} {i : Fin (n + 2)}
  (σ : (Λ[n + 1, i] : SSet.{max u v}) ⟶ DGNerve.pinchedHom R D x y)
  (q : ∀ k : ℤ, k = 1 - ((Finset.univ : Finset (Fin (n + 2))).card : ℤ) →
    GradedHom R x y k)

def dgGluingHornTopData : LinearData R x y (n + 1) :=
  pinchedReplaceTopData (fun t =>
    if hm : t.val.1 = Finset.univ.erase i then
      deletionSolution Finset.univ i
        (fun j => (HornData.knownData σ).componentOrZero (Finset.univ.erase j) t.val.2) +
        (deletionSign Finset.univ i)⁻¹ •
          (homObject R D x y).d (t.val.2 - 1) t.val.2
            (q (t.val.2 - 1) (by
              have := Finset.card_erase_add_one (Finset.mem_univ i)
              have hk := t.property.2
              rw [hm] at hk
              omega))
    else (HornData.knownData σ) t) q

lemma dgGluingHornTopData_known (J : Finset (Fin (n + 2))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hf : J ≠ Finset.univ) (hm : J ≠ Finset.univ.erase i) :
    (dgGluingHornTopData σ q).component J k hJ hk =
      (HornData.knownData σ).component J k hJ hk := by
  rw [dgGluingHornTopData, pinchedReplaceTopData_proper _ _ J k hJ hk hf]
  simp only [LinearData.component, dite_eq_right hm]

lemma dgGluingHornTopData_top (k : ℤ)
    (hk : k = 1 - ((Finset.univ : Finset (Fin (n + 2))).card : ℤ)) :
    (dgGluingHornTopData σ q).component Finset.univ k Finset.univ_nonempty hk = q k hk :=
  pinchedReplaceTopData_full _ _ k hk

lemma dgGluingHornTopData_missing (k : ℤ)
    (hk : k = 1 - ((Finset.univ : Finset (Fin (n + 2))).card : ℤ)) :
    (dgGluingHornTopData σ q).component (Finset.univ.erase i) (k + 1)
      (LinearData.erase_nonempty (by simp) i (Finset.mem_univ _))
      (by have := Finset.card_erase_add_one (Finset.mem_univ i); omega) =
      deletionSolution Finset.univ i
        (fun j => (HornData.knownData σ).componentOrZero (Finset.univ.erase j) (k + 1)) +
        (deletionSign Finset.univ i)⁻¹ • differential R (q k hk) := by
  have hf : (Finset.univ.erase i : Finset (Fin (n + 2))) ≠ Finset.univ :=
    (Finset.erase_ssubset (Finset.mem_univ i)).ne
  rw [dgGluingHornTopData, pinchedReplaceTopData_proper _ _ _ _ _ _ hf]
  simp only [LinearData.component, dite_true]
  congr 2
  have htransport : ∀ (l : ℤ) (hl : l = k)
      (hd : l = 1 - ((Finset.univ : Finset (Fin (n + 2))).card : ℤ)),
      (homObject R D x y).d l (k + 1) (q l hd) = differential R (q k hk) := by
    intro l hl
    subst l
    exact fun _ => rfl
  exact htransport (k + 1 - 1) (by omega) _

lemma dgGluingHornTopData_face (j : Fin (n + 2)) (hji : j ≠ i) :
    LinearData.pullback j.succAboveOrderEmb.toOrderHom (dgGluingHornTopData σ q) =
      HornData.faceData σ j hji := by
  rw [← HornData.knownData_pullback_face σ j hji]
  funext t
  rcases t with ⟨⟨J, k⟩, hJ, hk⟩
  change (LinearData.pullback j.succAboveOrderEmb.toOrderHom
    (dgGluingHornTopData σ q)).component J k hJ hk =
    (LinearData.pullback j.succAboveOrderEmb.toOrderHom
      (HornData.knownData σ)).component J k hJ hk
  rw [LinearData.pullback_component_of_inj _ _ _ _ _ _ j.succAboveOrderEmb.injective.injOn,
    LinearData.pullback_component_of_inj _ _ _ _ _ _ j.succAboveOrderEmb.injective.injOn]
  exact dgGluingHornTopData_known σ q _ _ _ _
    (HornData.image_known j hji J).1 (HornData.image_known j hji J).2

end SerrePositivity.InfinityCategories
