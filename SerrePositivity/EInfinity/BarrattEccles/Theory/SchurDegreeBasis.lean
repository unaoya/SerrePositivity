module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.SchurDegreeDecomposition
public import SerrePositivity.EInfinity.BarrattEccles.Theory.ArityFreeRepresentation
public import SerrePositivity.EInfinity.BarrattEccles.Sequence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.TensorBasis

/-!
# Schur 複体の次数付き基底の移送

## 概要
Berger–Fresse §1.1 の自由な対称群基底を、Berger–Moerdijk §1 の Schur 表示へ移す。

## 方針
各双次数の余不変の基底を余積し、Schur 複体の実際の次数成分へ移す。

## 規約
基底の添字と余積の指定包含を保持する。

## 使われ方
セル代数の単項式に重みを付ける際の次数ごとの基底。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.EInfinity

open CategoryTheory Limits MonoidalCategory HomologicalComplex DifferentialGraded

variable {A : Type u} [CommRing A]

/-- A specified basis of a coproduct of modules. -/
def moduleCoproductBasis {J : Type v} (V : J → ModuleCat.{max v u} A)
    {I : J → Type (max v u)}
    (b : ∀ j, Module.Basis (I j) A (V j)) :
    Module.Basis (Σ j, I j) A (∐ V : ModuleCat.{max v u} A) := by
  classical
  exact (DFinsupp.basis b).map (ModuleCat.coprodIsoDirectSum V).symm.toLinearEquiv

/-- The coproduct basis uses the specified inclusions on each basis vector. -/
lemma moduleCoproductBasis_apply {J : Type v} (V : J → ModuleCat.{max v u} A)
    {I : J → Type (max v u)}
    (b : ∀ j, Module.Basis (I j) A (V j)) (x : Σ j, I j) :
    moduleCoproductBasis V b x = Sigma.ι V x.1 (b x.1 x.2) := by
  classical
  change (ModuleCat.coprodIsoDirectSum V).inv
    (DFinsupp.basis b x) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.directSumBasis_apply]
  exact congrArg (fun f => f (b x.1 x.2))
    (ModuleCat.lof_coprodIsoDirectSum_inv V x.1)

/-- Specified bases in the arity and bidegree pieces give a basis of the actual Schur degree. -/
def schurDegreeBasis (P : SymmetricSequence (Complex A)) (K : Complex A) (i : ℤ)
    {I : (n : ℕ) → {a : ℤ × ℤ // a.1 + a.2 = i} → Type u}
    (b : ∀ n a, Module.Basis (I n a) A
      (schurArityBidegreeRepresentation P K i n a).ρ.Coinvariants) :
    Module.Basis (Σ n, Σ a, I n a) A (((schurFunctor A P).obj K).X i) := by
  classical
  let V n a := ModuleCat.of A (schurArityBidegreeRepresentation P K i n a).ρ.Coinvariants
  exact (moduleCoproductBasis (fun n => ∐ (V n))
    (fun n => moduleCoproductBasis (V n) (b n))).map
      (schurDegreeBidegreeIso P K i).symm.toLinearEquiv

namespace BarrattEccles

/-- The evaluated sequence action agrees with the regular arity action. -/
lemma complexDegreeRepresentation_sequence (n q : ℕ) :
    complexDegreeRepresentation (finiteBijectionComplexAction (sequence A) n) (-(q : ℤ)) =
      arityDegreeRepresentation A n q := by
  ext σ x
  change ((sequence A).map (FiniteBijection.permutation n σ.down)).f (-(q : ℤ)) x = _
  rw [sequence_map_permutation]
  rfl

/-- In a nonpositive coefficient degree, an arbitrary basis of the tensor-power factor
transfers to the diagonal coinvariants of the Schur bidegree. -/
def schurNonpositiveBidegreeBasis (K : Complex A) (i : ℤ) (n q : ℕ)
    {I : Type u} (b : Module.Basis I A
      ((TensorPowers.power K n).X (i + q))) :
    Module.Basis (ULift.{u} (BasedNondegenerate n q) × I) A
      (schurArityBidegreeRepresentation (sequence A) K i n
        ⟨(-(q : ℤ), i + q), by omega⟩).ρ.Coinvariants := by
  let V := Rep.of (complexDegreeRepresentation
    (finiteBijectionComplexAction (TensorPowers.bijectionFunctor K) n) (i + q))
  let U := Rep.of (complexDegreeRepresentation
    (finiteBijectionComplexAction (sequence A) n) (-(q : ℤ)))
  let e : U ≅ Rep.of (arityDegreeRepresentation A n q) :=
    eqToIso (congrArg Rep.of (complexDegreeRepresentation_sequence n q))
  let e' := (Rep.coinvariantsFunctor A _).mapIso
    ((β_ U V) ≪≫ (Iso.refl V ⊗ᵢ e))
  exact (arityDegreeCoinvariantsTensorBasis A n q V b).map e'.symm.toLinearEquiv

end BarrattEccles

end SerrePositivity.EInfinity
