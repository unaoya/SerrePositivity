module

public import Mathlib.FieldTheory.PerfectClosure
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.MvPolynomial.Basic
public import SerrePositivity.CommutativeAlgebra.PerfectRing
public import SerrePositivity.CommutativeAlgebra.DirectLimit
public import Mathlib.Algebra.MvPolynomial.Nilpotent

/-! # 自由な完全多項式代数

## 概要

完全標数 p の環上の自由な完全多項式代数 `PerfectPolynomial`（多項式環の完全閉包）を作り、完全標数 p 代数への評価が一意に延びること（`perfectPolynomialHomEquiv`）、標的の元すべてを変数にすれば全射な表示が得られること、完全な係数環上で平坦であることを示す。

## 方針

係数の作用は通常の多項式の包含で固定する。平坦性は、各変数の根を順に添加した段の加群としての有向極限が完全閉包と一致することから従う。

## 規約

`perfectPolynomialHomEquiv` は残す。instance `perfectPolynomialAlgebra`・`perfectPolynomialDirectedSystem` はビルドで使用を確認する。

## 使われ方

BhattScholze の perfect 環の表示と perfectoid 化。
-/

@[expose] public noncomputable section

universe u

section PerfectPolynomialPart

namespace SerrePositivity
variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] [CharP R p]

/-- The perfection of the polynomial ring on the specified variables. -/
abbrev PerfectPolynomial (σ : Type u) := PerfectClosure (MvPolynomial σ R) p

/-- The coefficient action through the standard polynomial inclusion. -/
instance perfectPolynomialAlgebra (σ : Type u) : Algebra R (PerfectPolynomial p R σ) :=
  ((PerfectClosure.of (MvPolynomial σ R) p).comp MvPolynomial.C).toAlgebra

/-- The perfect-closure lift preserves the original ring map. -/
lemma perfectClosure_lift_of {K S : Type u} [CommRing K] [CharP K p]
    [CommRing S] [CharP S p] [PerfectRing S p] (f : K →+* S) (x : K) :
    (PerfectClosure.lift K p S f) (PerfectClosure.of K p x) = f x := by
  exact congrArg (fun g : K →+* S => g x) ((PerfectClosure.lift K p S).symm_apply_apply f)

/-- Evaluation extends to the perfect closure as an R-algebra map. -/
def perfectPolynomialEval (σ S : Type u) [CommRing S] [Algebra R S]
    [CharP S p] [PerfectRing S p] (f : σ → S) : PerfectPolynomial p R σ →ₐ[R] S :=
  { PerfectClosure.lift (MvPolynomial σ R) p S (MvPolynomial.eval₂Hom (algebraMap R S) f) with
    commutes' := fun r => by
      change PerfectClosure.lift (MvPolynomial σ R) p S
        (MvPolynomial.eval₂Hom (algebraMap R S) f)
        (PerfectClosure.of (MvPolynomial σ R) p (MvPolynomial.C r)) = algebraMap R S r
      rw [perfectClosure_lift_of]
      exact MvPolynomial.eval₂_C _ _ _ }

/-- Evaluation sends each original variable to its prescribed value. -/
lemma perfectPolynomialEval_X (σ S : Type u) [CommRing S] [Algebra R S]
    [CharP S p] [PerfectRing S p] (f : σ → S) (s : σ) :
    perfectPolynomialEval p R σ S f
      (PerfectClosure.of (MvPolynomial σ R) p (MvPolynomial.X s)) = f s := by
  change PerfectClosure.lift (MvPolynomial σ R) p S
    (MvPolynomial.eval₂Hom (algebraMap R S) f)
    (PerfectClosure.of (MvPolynomial σ R) p (MvPolynomial.X s)) = f s
  rw [perfectClosure_lift_of]
  exact MvPolynomial.eval₂_X _ _ _

/-- Variables indexed by the target itself give a surjective presentation. -/
lemma perfectPolynomialEval_surjective (S : Type u) [CommRing S] [Algebra R S]
    [CharP S p] [PerfectRing S p] :
    Function.Surjective (perfectPolynomialEval p R S S id) := by
  intro s
  exact ⟨PerfectClosure.of (MvPolynomial S R) p (MvPolynomial.X s),
    perfectPolynomialEval_X p R S S id s⟩
/-- Maps to a perfect algebra are determined by their values on the variables. -/
lemma perfectPolynomial_hom_ext (σ S : Type u) [CommRing S] [Algebra R S]
    [CharP S p] [PerfectRing S p] {f g : PerfectPolynomial p R σ →ₐ[R] S}
    (h : ∀ s, f (PerfectClosure.of (MvPolynomial σ R) p (MvPolynomial.X s)) =
      g (PerfectClosure.of (MvPolynomial σ R) p (MvPolynomial.X s))) : f = g := by
  apply AlgHom.toRingHom_injective
  apply (PerfectClosure.lift (MvPolynomial σ R) p S).symm.injective
  apply MvPolynomial.ringHom_ext
  · intro r
    change f (algebraMap R (PerfectPolynomial p R σ) r) =
      g (algebraMap R (PerfectPolynomial p R σ) r)
    rw [f.commutes, g.commutes]
  · exact h

/-- The universal property of the free perfect polynomial algebra. -/
def perfectPolynomialHomEquiv (σ S : Type u) [CommRing S] [Algebra R S]
    [CharP S p] [PerfectRing S p] :
    (σ → S) ≃ (PerfectPolynomial p R σ →ₐ[R] S) where
  toFun := perfectPolynomialEval p R σ S
  invFun f s := f (PerfectClosure.of (MvPolynomial σ R) p (MvPolynomial.X s))
  left_inv f := by funext s; exact perfectPolynomialEval_X p R σ S f s
  right_inv f := by
    apply perfectPolynomial_hom_ext
    intro s
    exact perfectPolynomialEval_X p R σ S _ s

end SerrePositivity

end PerfectPolynomialPart

section PerfectPolynomialFlatPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] [CharP R p]
    [PerfectRing R p] (σ : Type u)
local notation "K" => MvPolynomial σ R
local notation "P" => PerfectPolynomial p R σ

/-- The nth stage sends variables to their canonical pⁿ-th roots. -/
def perfectPolynomialStage (n : ℕ) : K →ₐ[R] P :=
  MvPolynomial.aeval (fun s => (iterateFrobeniusEquiv P p n).symm
    (PerfectClosure.of K p (MvPolynomial.X s)))

/-- Frobenius of a stage map is the ordinary inclusion with twisted coefficients. -/
lemma perfectPolynomialStage_frobenius (n : ℕ) (f : K) :
    iterateFrobeniusEquiv P p n (perfectPolynomialStage p R σ n f) =
    PerfectClosure.of K p (MvPolynomial.map (iterateFrobeniusEquiv R p n).toRingHom f) := by
  have h : (iterateFrobeniusEquiv P p n).toRingHom.comp (perfectPolynomialStage p R σ n).toRingHom =
      (PerfectClosure.of K p).comp (MvPolynomial.map (iterateFrobeniusEquiv R p n).toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        perfectPolynomialStage, MvPolynomial.aeval_C, MvPolynomial.map_C]
      change iterateFrobeniusEquiv P p n (PerfectClosure.of K p (MvPolynomial.C r)) = _
      change _ = PerfectClosure.of K p (MvPolynomial.C (iterateFrobeniusEquiv R p n r))
      simp only [iterateFrobeniusEquiv_def, map_pow]
    · intro s
      change iterateFrobeniusEquiv P p n (perfectPolynomialStage p R σ n (MvPolynomial.X s)) = _
      rw [perfectPolynomialStage, MvPolynomial.aeval_X, RingHom.comp_apply, MvPolynomial.map_X]
      exact (iterateFrobeniusEquiv P p n).apply_symm_apply _
  exact congrArg (fun h : K →+* P => h f) h

/-- The original polynomial ring embeds in its perfect closure over a perfect base. -/
lemma perfectPolynomial_of_injective : Function.Injective (PerfectClosure.of K p) := by
  have : IsReduced R := isReduced_of_perfectPower R p (Fact.out : p.Prime).one_lt
  intro x y h
  exact (PerfectClosure.eq_iff K p (0, x) (0, y)).mp h

/-- Every polynomial stage embeds in the original perfect closure. -/
lemma perfectPolynomialStage_injective (n : ℕ) :
    Function.Injective (perfectPolynomialStage p R σ n) := by
  intro x y h
  apply MvPolynomial.map_injective _ (iterateFrobeniusEquiv R p n).injective
  apply perfectPolynomial_of_injective p R σ
  exact (perfectPolynomialStage_frobenius p R σ n x).symm.trans
    ((congrArg (iterateFrobeniusEquiv P p n) h).trans (perfectPolynomialStage_frobenius p R σ n y))

/-- The transition fixes coefficients and sends each variable to its p-th power. -/
def perfectPolynomialStep : K →ₐ[R] K := MvPolynomial.aeval (fun s => MvPolynomial.X s ^ p)

omit [PerfectRing R p] in
/-- Successive stage maps commute with the variable-power transition. -/
lemma perfectPolynomialStage_step (n : ℕ) (f : K) :
    perfectPolynomialStage p R σ (n + 1) (perfectPolynomialStep p R σ f) =
      perfectPolynomialStage p R σ n f := by
  have h : (perfectPolynomialStage p R σ (n + 1)).comp (perfectPolynomialStep p R σ) =
      perfectPolynomialStage p R σ n := by
    apply MvPolynomial.algHom_ext
    intro s
    simp only [AlgHom.comp_apply, perfectPolynomialStep, MvPolynomial.aeval_X,
      map_pow, perfectPolynomialStage]
    rw [iterateFrobeniusEquiv_symm_add_apply]
    rw [← map_pow, iterateFrobeniusEquiv_one, frobeniusEquiv_symm_pow_p]
  exact congrArg (fun h : K →ₐ[R] P => h f) h

/-- The transition between arbitrary polynomial stages. -/
def perfectPolynomialTransition (i j : ℕ) (_ : i ≤ j) : K →ₗ[R] K :=
  (perfectPolynomialStep p R σ).toLinearMap ^ (j - i)

/-- These polynomial transitions form a directed system. -/
instance perfectPolynomialDirectedSystem :
    DirectedSystem (fun _ : ℕ => K) (perfectPolynomialTransition p R σ · · ·) where
  map_self := by intro i x; simp [perfectPolynomialTransition]
  map_map := by
    intro k j i hij hjk x
    dsimp only [perfectPolynomialTransition]
    rw [← Module.End.mul_apply, ← pow_add, Nat.sub_add_sub_cancel hjk hij]

omit [PerfectRing R p] in
/-- All directed transitions preserve the maps to the perfect closure. -/
lemma perfectPolynomialStage_transition (i j : ℕ) (hij : i ≤ j) (f : K) :
    perfectPolynomialStage p R σ j (perfectPolynomialTransition p R σ i j hij f) =
      perfectPolynomialStage p R σ i f := by
  induction j, hij using Nat.le_induction with
  | base => simp [perfectPolynomialTransition]
  | succ j hij ih =>
    rw [perfectPolynomialTransition, Nat.succ_sub hij, pow_succ', Module.End.mul_apply]
    change perfectPolynomialStage p R σ (j + 1) (perfectPolynomialStep p R σ _) = _
    rw [perfectPolynomialStage_step]
    exact ih

/-- Every element of the perfect closure comes from a polynomial stage. -/
lemma perfectPolynomialStage_jointly_surjective :
    ∀ x : P, ∃ n f, perfectPolynomialStage p R σ n f = x := by
  intro x
  obtain ⟨⟨n, f⟩, rfl⟩ := PerfectClosure.mk_surjective K p x
  refine ⟨n, MvPolynomial.map (iterateFrobeniusEquiv R p n).symm.toRingHom f, ?_⟩
  apply (iterateFrobeniusEquiv P p n).injective
  rw [perfectPolynomialStage_frobenius]
  have hf : MvPolynomial.map (iterateFrobeniusEquiv R p n).toRingHom
      (MvPolynomial.map (iterateFrobeniusEquiv R p n).symm.toRingHom f) = f := by
    rw [MvPolynomial.map_map]
    have hcomp : (iterateFrobeniusEquiv R p n).toRingHom.comp
        (iterateFrobeniusEquiv R p n).symm.toRingHom = RingHom.id R := by
      ext r
      exact (iterateFrobeniusEquiv R p n).apply_symm_apply r
    rw [hcomp, MvPolynomial.map_id]
  rw [hf]
  simpa only [iterate_frobenius, iterateFrobeniusEquiv_def] using
    (PerfectClosure.iterate_frobenius_mk K p n f).symm

/-- The canonical R-linear map from the actual module direct limit. -/
def perfectPolynomialLimitMap :
    Module.DirectLimit (fun _ : ℕ => K) (perfectPolynomialTransition p R σ) →ₗ[R] P :=
  Module.DirectLimit.lift R ℕ (fun _ : ℕ => K) (perfectPolynomialTransition p R σ)
    (fun n => (perfectPolynomialStage p R σ n).toLinearMap)
    (perfectPolynomialStage_transition p R σ)

/-- The canonical limit map is both injective and surjective. -/
lemma perfectPolynomialLimitMap_bijective :
    Function.Bijective (perfectPolynomialLimitMap p R σ) := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    obtain ⟨n, f, rfl⟩ := Module.DirectLimit.exists_of x
    have hf : perfectPolynomialStage p R σ n f = 0 := by
      simpa only [perfectPolynomialLimitMap, Module.DirectLimit.lift_of, AlgHom.toLinearMap_apply]
        using hx
    have hf0 : f = 0 := (perfectPolynomialStage_injective p R σ n) (hf.trans (map_zero _).symm)
    rw [hf0, map_zero]
  · intro x
    obtain ⟨n, f, rfl⟩ := perfectPolynomialStage_jointly_surjective p R σ x
    exact ⟨Module.DirectLimit.of R ℕ (fun _ : ℕ => K) (perfectPolynomialTransition p R σ) n f,
      Module.DirectLimit.lift_of ..⟩

/-- The actual polynomial module direct limit is the perfect closure over R. -/
def perfectPolynomialLimitEquiv :
    Module.DirectLimit (fun _ : ℕ => K) (perfectPolynomialTransition p R σ) ≃ₗ[R] P :=
  LinearEquiv.ofBijective (perfectPolynomialLimitMap p R σ)
    (perfectPolynomialLimitMap_bijective p R σ)

/-- A free perfect polynomial algebra over a perfect base is flat over that base. -/
lemma perfectPolynomial_flat : Module.Flat R P := by
  have : Module.Flat R (Module.DirectLimit (fun _ : ℕ => K) (perfectPolynomialTransition p R σ)) :=
    moduleDirectLimit_flat (fun _ : ℕ => K) (perfectPolynomialTransition p R σ)
  exact Module.Flat.of_linearEquiv (perfectPolynomialLimitEquiv p R σ).symm
end SerrePositivity

end PerfectPolynomialFlatPart
