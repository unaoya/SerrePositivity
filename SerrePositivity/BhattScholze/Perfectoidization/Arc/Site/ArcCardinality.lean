module

public import SerrePositivity.BhattScholze.Perfectoidization.Construction.RootAdjunction
public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Descent.ArcPerfectoidBase
public import Mathlib.Algebra.MvPolynomial.Cardinal
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# arc site のための濃度評価

## 概要
根添加の塔と完備底変換に対し、始域の濃度と可算冪で上界を与える。

## 方針
導来主元完備化の H⁰ を可算列の商として評価する。
根添加では多項式環と可算余極限を、底変換ではテンソルの有限和表示を使う。

## 規約
導来完備化の H⁰ を使い、p 冪ねじれの有界性を仮定しない。

## 使われ方
BS 著者版 Lemma 8.8 の affine 版で被覆の対象を所定の濃度以下に取る。
-/

@[expose] public noncomputable section

universe u
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Cardinal
open scoped _root_.Cardinal _root_.TensorProduct

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open _root_.SerrePositivity.BhattScholze.PerfectoidizationInterface
open _root_.SerrePositivity.DerivedCompletion

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.card_le_countable_power (a : Cardinal) : a ≤ a ^ ℵ₀ :=
  Cardinal.self_le_power _ one_le_aleph0

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.countable_power_idempotent (a : Cardinal) : (a ^ ℵ₀) ^ ℵ₀ = a ^ ℵ₀ := by
  rw [← Cardinal.power_mul, Cardinal.mul_eq_self le_rfl]

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.mk_countable_sequences (S : Type u) : #(ℕ → S) = #S ^ ℵ₀ := by
  simp

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completionRing_cardinal_le (p : ℕ) (S : CommRingCat.{u}) :
    #(completionRing p S : Type u) ≤ #S ^ ℵ₀ := by
  change #(PrincipalCompletionH0 S (p : S)) ≤ _
  rw [Cardinal.mk_congr (principalCompletionH0Equiv S (p : S)).toEquiv,
    ← _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.mk_countable_sequences S]
  exact Cardinal.mk_le_of_surjective (Submodule.mkQ_surjective _)

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.rootAdjunctionStep_cardinal_le (p : ℕ) (R S : Type u) [CommRing R] [CommRing S]
    {κ : Cardinal.{u}} (hinf : ℵ₀ ≤ κ) (hκ : κ ^ ℵ₀ = κ) (hS : #S ≤ κ) :
    #(_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootAdjunctionStep p R S) ≤ κ := by
  have hsum : #(S ⊕ S) ≤ κ := by
    simp only [Cardinal.mk_sum, Cardinal.lift_id]
    exact (add_le_add hS hS).trans_eq (by rw [Cardinal.add_eq_max hinf, max_self])
  have hpoly : #(MvPolynomial (S ⊕ S) S) ≤ κ :=
    MvPolynomial.cardinalMk_le_max.trans (sup_le (sup_le hS hsum) hinf)
  have hquot : #(MvPolynomial (S ⊕ S) S ⧸ _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepIdeal p (CommRingCat.of S)) ≤ κ :=
    (Cardinal.mk_le_of_surjective Ideal.Quotient.mk_surjective).trans hpoly
  exact (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completionRing_cardinal_le p _).trans
    ((Cardinal.power_le_power_right hquot).trans_eq hκ)

/-- 根添加の可算塔とその導来 p 完備化の濃度評価。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.rootClosure_cardinal_le (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R]
    (S : Type u) [CommRing S] [Algebra R S] :
    #(_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootClosure p R S) ≤ (#S + ℵ₀) ^ ℵ₀ := by
  let c := #S + ℵ₀
  let κ := c ^ ℵ₀
  have hS : #S ≤ c := by dsimp [c]; exact le_self_add
  have hc : ℵ₀ ≤ c := by dsimp [c]; exact le_add_self
  have hcκ : c ≤ κ := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.card_le_countable_power c
  have hκ : ℵ₀ ≤ κ := hc.trans hcκ
  have hκpow : κ ^ ℵ₀ = κ := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.countable_power_idempotent c
  have hstage (n : ℕ) : #((_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedStages p R S n : CommRingCat.{u}) : Type u) ≤ κ := by
    induction n with
    | zero => exact hS.trans hcκ
    | succ n ih => exact _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.rootAdjunctionStep_cardinal_le p R _ hκ hκpow ih
  let F := _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedRootTower p R S
  have hcolim : #(colimit F : CommRingCat.{u}) ≤ κ := by
    let : PreservesFilteredColimitsOfSize.{0, 0} (forget CommRingCat.{u}) :=
      preservesSmallestFilteredColimits_of_preservesFilteredColimits _
    let f : (Σ n : ℕ, (F.obj n : Type u)) → (colimit F : CommRingCat.{u}) :=
      fun x => colimit.ι F x.1 x.2
    have hf : Function.Surjective f := Concrete.from_union_surjective_of_isColimit F
      (colimit.isColimit F)
    apply (Cardinal.mk_le_of_surjective hf).trans
    rw [Cardinal.mk_sigma]
    apply (Cardinal.sum_le_lift_mk_mul_iSup _).trans
    rw [Cardinal.mk_nat, Cardinal.lift_aleph0]
    exact (mul_le_mul_right (ciSup_le hstage) _).trans_eq (Cardinal.aleph0_mul_eq hκ)
  exact (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completionRing_cardinal_le p (colimit F)).trans
    ((Cardinal.power_le_power_right hcolim).trans_eq hκpow)

variable (p : ℕ) [Fact p.Prime]

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.padicInt_cardinal_le : #(PadicInt p) ≤ ℵ₀ ^ ℵ₀ := by
  have h₁ : #(PadicInt p) ≤ #(Padic p) := Cardinal.mk_le_of_injective Subtype.val_injective
  have h₂ : #(Padic p) ≤ #(PadicSeq p) := Cardinal.mk_quotient_le
  have h₃ : #(PadicSeq p) ≤ #(ℕ → ℚ) := Cardinal.mk_le_of_injective Subtype.val_injective
  exact (h₁.trans (h₂.trans h₃)).trans_eq (by
    rw [_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.mk_countable_sequences, Cardinal.mk_eq_aleph0 ℚ])

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.perfectoidBaseRing_cardinal_le :
    #(_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.perfectoidBaseRing.{u} p) ≤ ℵ₀ ^ ℵ₀ := by
  let κ : Cardinal.{u} := ℵ₀ ^ ℵ₀
  have hκ : ℵ₀ ≤ κ := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.card_le_countable_power ℵ₀
  have hpadic : #(ULift.{u} (PadicInt p)) ≤ κ := by
    simpa only [Cardinal.mk_uLift, Cardinal.lift_power, Cardinal.lift_aleph0] using
      (Cardinal.lift_le.mpr (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.padicInt_cardinal_le p))
  have hpoly : #(_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootPolynomial.{u} p) ≤ κ := by
    apply MvPolynomial.cardinalMk_le_max_lift.trans
    simpa only [Cardinal.lift_uzero, Cardinal.mk_nat, Cardinal.lift_aleph0] using
      (sup_le (sup_le hpadic hκ) hκ)
  have hquot : #(_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcRootQuotient.{u} p) ≤ κ :=
    (Cardinal.mk_le_of_surjective Ideal.Quotient.mk_surjective).trans hpoly
  exact (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completionRing_cardinal_le p _).trans
    ((Cardinal.power_le_power_right hquot).trans_eq (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.countable_power_idempotent ℵ₀))

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.tensorProduct_cardinal_le {A : Type*} (S T : Type u) [CommRing A]
    [CommRing S] [CommRing T] [Algebra A S] [Algebra A T] {κ : Cardinal.{u}}
    (hinf : ℵ₀ ≤ κ) (hS : #S ≤ κ) (hT : #T ≤ κ) : #(S ⊗[A] T) ≤ κ := by
  let f : List (S × T) → S ⊗[A] T :=
    fun l => (l.map (fun st => st.1 ⊗ₜ[A] st.2)).sum
  have hf : Function.Surjective f := by
    intro z
    refine _root_.TensorProduct.inductionOn (motive := fun z => ∃ l, f l = z) z ?_ ?_
    · intro x y
      exact ⟨[(x, y)], by simp [f]⟩
    · rintro x y ⟨lx, rfl⟩ ⟨ly, rfl⟩
      exact ⟨lx ++ ly, by simp [f]⟩
  apply (Cardinal.mk_le_of_surjective hf).trans
  apply (Cardinal.mk_list_le_max _).trans
  refine max_le hinf ?_
  simp only [Cardinal.mk_prod, Cardinal.lift_id]
  exact (mul_le_mul' hS hT).trans_eq (Cardinal.mul_eq_self hinf)

/-- 完備な底変換の濃度は可算個のデータで評価できる。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.baseExtension_cardinal_le (S : Type u) [CommRing S]
    (hS : IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    #(_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.baseExtension p S hS) ≤ (#S + ℵ₀) ^ ℵ₀ := by
  let c := #S + ℵ₀
  let κ := c ^ ℵ₀
  have hSc : #S ≤ c := le_self_add
  have hc : ℵ₀ ≤ c := le_add_self
  have hcκ : c ≤ κ := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.card_le_countable_power c
  have hR₀ : #(_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.perfectoidBaseRing.{u} p) ≤ κ :=
    (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.perfectoidBaseRing_cardinal_le p).trans (Cardinal.power_le_power_right hc)
  have hT : #(_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.arcBaseTensor p S hS : Type u) ≤ κ := by
    let : Algebra (PadicInt p) S := (_root_.SerrePositivity.BhattScholze.Perfectoidization.Derived.arcPadicIntMap p S hS).toAlgebra
    exact _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.tensorProduct_cardinal_le S (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.perfectoidBaseRing p) (hc.trans hcκ) (hSc.trans hcκ) hR₀
  exact (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.completionRing_cardinal_le p _).trans
    ((Cardinal.power_le_power_right hT).trans_eq (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.countable_power_idempotent c))

end SerrePositivity.BhattScholze.Perfectoidization.Derived
