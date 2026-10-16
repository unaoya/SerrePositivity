module
public import SerrePositivity.DifferentialGraded.Complexes.Cells
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # dg加群のcompact性に使う余積の有限support表示 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] {J : Type u}

/-- 任意の加群の余積cofanの元は、有限個の包含の像の和である。 -/
lemma moduleCofan_element_rep (F : J → ModuleCat.{u} A) (s : Cofan F)
    (hs : IsColimit s) (z : s.pt) :
    ∃ (t : Finset J) (c : ∀ j, F j), ∑ j ∈ t, s.inj j (c j) = z := by
  classical
  let e := (ModuleCat.coproductCoconeIsColimit F).coconePointUniqueUpToIso hs
  let w : DirectSum J (fun j => F j) := e.inv z
  have hi (j : J) (a : F j) : e.hom (DirectSum.of (fun j => F j) j a) = s.inj j a := by
    have h := (ModuleCat.coproductCoconeIsColimit F).comp_coconePointUniqueUpToIso_hom hs ⟨j⟩
    exact congrArg (fun k => k a) h
  have hw : e.hom w = z := by
    change e.hom (e.inv z) = z
    rw [← ModuleCat.comp_apply, e.inv_hom_id, ModuleCat.id_apply]
  have h := congrArg e.hom.hom (DirectSum.sum_support_of w)
  simp only [map_sum, hi, hw] at h
  exact ⟨w.support, fun j => w j, h⟩

/-- 次数ごとの余積表示。複体は非有界でよい。 -/
lemma complexCofan_element_rep (F : J → Complex A) (s : Cofan F) (hs : IsColimit s)
    (n : ℤ) (z : s.pt.X n) :
    ∃ (t : Finset J) (c : ∀ j, (F j).X n), ∑ j ∈ t, (s.inj j).f n (c j) = z := by
  let ev := HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) n
  have hn : IsColimit (Cofan.mk (s.pt.X n) (fun j => (s.inj j).f n)) :=
    isColimitCofanMkObjOfIsColimit ev F s.inj hs
  exact moduleCofan_element_rep A (fun j => (F j).X n) _ hn z

/-- cycleも有限個の成分cycleの像の和になる。 -/
lemma complexCofan_cycle_rep (F : J → Complex A) (s : Cofan F) (hs : IsColimit s)
    (n : ℤ) (z : complexCycles A s.pt n) :
    ∃ (t : Finset J) (c : ∀ j, complexCycles A (F j) n),
      ∑ j ∈ t, (s.inj j).f n (c j).val = z.val := by
  classical
  let pr (j : J) : s.pt ⟶ F j := hs.desc (Cofan.mk (F j) (Pi.single j (𝟙 (F j))))
  have hself (j : J) : s.inj j ≫ pr j = 𝟙 (F j) := by
    have h := hs.fac (Cofan.mk (F j) (Pi.single j (𝟙 (F j)))) ⟨j⟩
    change s.inj j ≫ pr j = (Pi.single j (𝟙 (F j)) : ∀ i, F i ⟶ F j) j at h
    rw [Pi.single_eq_same] at h
    exact h
  have hne (i j : J) (hij : i ≠ j) : s.inj i ≫ pr j = 0 := by
    have h := hs.fac (Cofan.mk (F j) (Pi.single j (𝟙 (F j)))) ⟨i⟩
    change s.inj i ≫ pr j = (Pi.single j (𝟙 (F j)) : ∀ i, F i ⟶ F j) i at h
    rw [Pi.single_eq_of_ne hij] at h
    exact h
  let c (j : J) : complexCycles A (F j) n :=
    ⟨(pr j).f n z.val, by
      have h := congrArg (fun k => k z.val) ((pr j).comm n (n + 1))
      change (F j).d n (n + 1) ((pr j).f n z.val) = 0
      change (F j).d n (n + 1) ((pr j).f n z.val) =
        (pr j).f (n + 1) (s.pt.d n (n + 1) z.val) at h
      have hz : s.pt.d n (n + 1) z.val = 0 := z.property
      rw [hz, map_zero] at h
      exact h⟩
  obtain ⟨t, b, hb⟩ := complexCofan_element_rep A F s hs n z.val
  have hc (j : J) (hj : j ∈ t) : (c j).val = b j := by
    change (pr j).f n z.val = b j
    rw [← hb, map_sum]
    calc
      _ = (pr j).f n ((s.inj j).f n (b j)) := Finset.sum_eq_single j
        (fun i _ hij => by
          rw [← ModuleCat.comp_apply, ← HomologicalComplex.comp_f, hne i j hij]
          rfl)
        (fun h => (h hj).elim)
      _ = b j := by
        rw [← ModuleCat.comp_apply, ← HomologicalComplex.comp_f, hself j]
        rfl
  refine ⟨t, c, ?_⟩
  calc
    _ = ∑ j ∈ t, (s.inj j).f n (b j) := Finset.sum_congr rfl (fun j hj => by rw [hc j hj])
    _ = z.val := hb

end SerrePositivity.DifferentialGraded
