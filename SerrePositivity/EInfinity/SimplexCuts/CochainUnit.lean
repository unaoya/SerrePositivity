module

public import SerrePositivity.EInfinity.SimplexCuts.UnaryCutUnit
public import SerrePositivity.EInfinity.SimplexCuts.SimplexGeneratorLinearExt
public import SerrePositivity.EInfinity.SimplexCuts.CochainInsertionCutSum
public import SerrePositivity.EInfinity.Surjection.ComplexUnit

/-!
# BF切断余作用の全複体射の単位則

Berger–Fresse §2.2.6、M14 L17、報告 §392。
元の一文字語の唯一Cutと指定左単位子を全入力次数で評価する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 同じ一文字語の作用を元の生成元の次数で読む（BF §2.2.6）。 -/
lemma cochainAction_unit_generator (S : SSet.{0}) {q : ℕ} (x : S _⦋q⦌) :
    (cochainAction A S 1).f (-(q : ℤ))
      (ιTensorObj (Surjection.complex A 1) (chains A S) 0 (-(q : ℤ)) (-(q : ℤ)) (zero_add _)
        ((Surjection.complexXIso A 1 0).inv (Surjection.unitElement A) ⊗ₜ[A] gen A S q x)) =
      (oneIso (chains A S)).inv.f (-(q : ℤ)) (gen A S q x) := by
  let u := Surjection.permutationWord (1 : Equiv.Perm (Fin 1))
  let s : Cut 0 q := ⟨∅, rfl⟩
  have hunique (t : Cut 0 q) : t = s := Subtype.ext (Finset.card_eq_zero.mp t.property)
  erw [cochainAction_basis_cut_sum A S u x (-(q : ℤ)) (by omega)]
  rw [Finset.sum_eq_single s]
  · rw [unaryCut_sign s (positiveWord u), one_smul]
    let f := cutGeneratorFamily A S s (positiveWord u) x
    have ht : -(vectorDegree (chains A S) 1 f : ℤ) = -(q : ℤ) := by
      rw [vectorDegree_cutGeneratorFamily]
      omega
    have hg : -(vectorDegree (chains A S) 1
        (fun _ => (⟨q, gen A S q x⟩ : Σ d : ℕ, (chains A S).X (-(d : ℤ)))) : ℤ) =
        -(q : ℤ) := by simp [vectorDegree, degreeSum]
    have H := vectorTensorAt_congr (chains A S) 1 f
      (fun _ => ⟨q, gen A S q x⟩) (-(q : ℤ)) ht hg
      (unaryCut_generatorFamily A S s (positiveWord u) x)
    exact H.trans (vectorTensorAt_one A (chains A S) ⟨q, gen A S q x⟩ (-(q : ℤ)) rfl)
  · intro t _ hts
    exact False.elim (hts (hunique t))
  · intro hs
    exact False.elim (hs (Finset.mem_univ s))

/-- 同じ単位係数を前置した全複体射は一次テンソル冪の標準同型（BF §2.2.6）。 -/
lemma cochainAction_unit_inv (S : SSet.{0}) :
    (λ_ (chains A S)).inv ≫ (Surjection.complexUnit A ▷ chains A S) ≫ cochainAction A S 1 =
      (oneIso (chains A S)).inv := by
  apply HomologicalComplex.hom_ext
  intro t
  by_cases ht : 0 < t
  · have hz : Limits.IsZero ((chains A S).X t) := by
      apply HomologicalComplex.isZero_extend_X
      intro q
      change -(q : ℤ) ≠ t
      omega
    let _ := ModuleCat.isZero_iff_subsingleton.mp hz
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    have hy : y = 0 := Subsingleton.elim _ _
    simp only [HomologicalComplex.comp_f, hy, map_zero]
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, t = -(q : ℤ) := ⟨(-t).toNat, by omega⟩
  apply ModuleCat.hom_ext
  apply chains_generator_linear_ext A S q
  intro x
  change (cochainAction A S 1).f (-(q : ℤ))
    ((Surjection.complexUnit A ▷ chains A S).f (-(q : ℤ))
      ((λ_ (chains A S)).inv.f (-(q : ℤ)) (gen A S q x))) = _
  rw [BarrattEccles.cochain_leftUnitor_inv_apply A,
    SerrePositivity.DifferentialGraded.whiskerRight_apply,
    Surjection.complexUnit_zero_apply, one_smul]
  exact cochainAction_unit_generator A S x

/-- L17：元のBF複体射の単位公理（BF §2.2.6）。 -/
lemma cochainAction_unit (S : SSet.{0}) :
    (Surjection.complexUnit A ▷ chains A S) ≫ cochainAction A S 1 ≫ (oneIso (chains A S)).hom =
      (λ_ (chains A S)).hom := by
  apply (cancel_epi (λ_ (chains A S)).inv).mp
  simpa only [Category.assoc, Iso.inv_hom_id] using
    congrArg (fun f => f ≫ (oneIso (chains A S)).hom) (cochainAction_unit_inv A S)

end SerrePositivity.EInfinity.SimplexCuts
