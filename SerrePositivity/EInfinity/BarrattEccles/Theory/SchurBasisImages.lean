module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.SchurWordBasis
public import SerrePositivity.EInfinity.BarrattEccles.Theory.SchurDegreeInclusions

/-!
# Schur の語の基底ベクトルと指定包含

## 概要
Berger–Fresse §1.1 の arity の自由基底を、Schur 複体の指定包含と照合する。

## 方針
余積の基底と余不変の基底の移送を、それぞれの指定同型で読む。

## 規約
係数の基点つき単体と入力の語の添字を保持する。

## 使われ方
セル代数の微分と入力の重みの照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory Limits HomologicalComplex DifferentialGraded
variable {A : Type u} [CommRing A]

/-- A specified Schur basis vector is the image of its two coproduct inclusions. -/
lemma schurDegreeBasis_apply (P : SymmetricSequence (Complex A)) (K : Complex A) (i : ℤ)
    {I : (n : ℕ) → {a : ℤ × ℤ // a.1 + a.2 = i} → Type u}
    (b : ∀ n a, Module.Basis (I n a) A
      (schurArityBidegreeRepresentation P K i n a).ρ.Coinvariants)
    (n : ℕ) (a : {a : ℤ × ℤ // a.1 + a.2 = i}) (x : I n a) :
    schurDegreeBasis P K i b ⟨n, a, x⟩ =
      (schurDegreeBidegreeIso P K i).inv
        (Sigma.ι (fun n => ∐ (fun a => ModuleCat.of A
          (schurArityBidegreeRepresentation P K i n a).ρ.Coinvariants)) n
          (Sigma.ι (fun a => ModuleCat.of A
            (schurArityBidegreeRepresentation P K i n a).ρ.Coinvariants) a (b n a x))) := by
  change (schurDegreeBidegreeIso P K i).inv
    (moduleCoproductBasis _ (fun n => moduleCoproductBasis _ (b n)) ⟨n, a, x⟩) = _
  rw [moduleCoproductBasis_apply, moduleCoproductBasis_apply]

namespace BarrattEccles
open MonoidalCategory
open scoped TensorProduct

/-- The diagonal coinvariant basis is the inverse image of a specified finitely supported basis. -/
lemma arityDegreeCoinvariantsTensorBasis_apply (n q : ℕ)
    (V : Rep.{u} A (ULift.{u} (Equiv.Perm (Fin n)))) {I : Type u}
    (b : Module.Basis I A V) (x : ULift.{u} (BasedNondegenerate n q) × I) :
    arityDegreeCoinvariantsTensorBasis A n q V b x =
      (arityDegreeCoinvariantsTensorEquiv A n q V).symm
        (Finsupp.single x.1 (b x.2)) := by
  classical
  simp only [arityDegreeCoinvariantsTensorBasis, Module.Basis.reindex_apply,
    Equiv.sigmaEquivProd_symm_apply, Module.Basis.map_apply, Finsupp.coe_basis]

/-- A diagonal coinvariant basis vector has its normalized coefficient at the identity. -/
lemma arityDegreeCoinvariantsTensorBasis_eq_mk (n q : ℕ)
    (V : Rep.{u} A (ULift.{u} (Equiv.Perm (Fin n)))) {I : Type u}
    (b : Module.Basis I A V) (x : ULift.{u} (BasedNondegenerate n q) × I) :
    arityDegreeCoinvariantsTensorBasis A n q V b x =
      Representation.Coinvariants.mk
        (V ⊗ Rep.of (arityDegreeRepresentation A n q)).ρ
        (b x.2 ⊗ₜ[A] equivariantBasis A n q (x.1, 1)) := by
  classical
  rw [arityDegreeCoinvariantsTensorBasis_apply]
  change (((Rep.coinvariantsTensor A _).obj V).map (arityDegreeFreeIso A n q).hom)
    (Rep.finsuppToCoinvariantsTensorFree V _ (Finsupp.single x.1 (b x.2))) = _
  rw [Rep.finsuppToCoinvariantsTensorFree_single]
  change Representation.Coinvariants.mk _
    (b x.2 ⊗ₜ[A] (arityDegreeFreeIso A n q).hom.hom
      (Finsupp.single x.1 (MonoidAlgebra.single 1 1))) = _
  congr 1
  congr 1
  change (arityDegreeFreeMap A n q).hom.toLinearMap
    (Finsupp.single x.1 (MonoidAlgebra.single 1 1)) = _
  rw [arityDegreeFreeMap_eq]
  rw [show Finsupp.single x.1 (MonoidAlgebra.single 1 1) =
      (Finsupp.basis (fun _ => MonoidAlgebra.basis
        (ULift.{u} (Equiv.Perm (Fin n))) A)) ⟨x.1, 1⟩ by
    simp [Finsupp.coe_basis, MonoidAlgebra.basis_apply]]
  rw [LinearEquiv.coe_coe, arityDegreeFreeLinearEquiv, Module.Basis.equiv_apply]
  simp

/-- The normalized representative in a Schur bidegree has the coefficient factor first. -/
lemma schurNonpositiveBidegreeBasis_eq_mk (K : Complex A) (i : ℤ) (n q : ℕ)
    {I : Type u} (b : Module.Basis I A ((TensorPowers.power K n).X (i + q)))
    (x : ULift.{u} (BasedNondegenerate n q) × I) :
    schurNonpositiveBidegreeBasis K i n q b x =
      Representation.Coinvariants.mk
        (schurArityBidegreeRepresentation (sequence A) K i n
          ⟨(-(q : ℤ), i + q), by omega⟩).ρ
        (equivariantBasis A n q (x.1, 1) ⊗ₜ[A] b x.2) := by
  classical
  rw [schurNonpositiveBidegreeBasis, Module.Basis.map_apply,
    arityDegreeCoinvariantsTensorBasis_eq_mk]
  change Representation.Coinvariants.mk _
    (equivariantBasis A n q (x.1, 1) ⊗ₜ[A] b x.2) = _
  rfl

/-- A normalized coefficient simplex and an input word give a Schur word index. -/
def schurNonpositiveWordIndex {I : ℤ → Type u} (i : ℤ) (n q : ℕ)
    (x : ULift.{u} (BasedNondegenerate n q) × powerGradedIndex I n (i + q)) :
    SchurWordIndex I i := by
  classical
  refine ⟨n, ⟨(-(q : ℤ), i + q), by omega⟩, ?_⟩
  simpa only [schurWordPieceIndex, ite_eq_left (show -(q : ℤ) ≤ 0 by omega),
    neg_neg, Int.toNat_natCast] using x

/-- The word basis in a normalized nonpositive bidegree is the specified coinvariant basis. -/
lemma schurWordPieceBasis_nonpositive {K : Complex A} {I : ℤ → Type u}
    (b : ∀ i, Module.Basis (I i) A (K.X i)) (i : ℤ) (n q : ℕ)
    (x : ULift.{u} (BasedNondegenerate n q) × powerGradedIndex I n (i + q)) :
    schurWordPieceBasis b i n ⟨(-(q : ℤ), i + q), by omega⟩
      (schurNonpositiveWordIndex i n q x).2.2 =
        schurNonpositiveBidegreeBasis K i n q (powerGradedBasis b n (i + q)) x := by
  classical
  cases q <;> simp [schurWordPieceBasis, schurNonpositiveWordIndex] <;> rfl

/-- A normalized word basis vector is the actual homogeneous Schur generator. -/
lemma schurWordBasis_nonpositive {K : Complex A} {I : ℤ → Type u}
    (b : ∀ i, Module.Basis (I i) A (K.X i)) (i : ℤ) (n q : ℕ)
    (x : ULift.{u} (BasedNondegenerate n q) × powerGradedIndex I n (i + q)) :
    schurWordBasis b i (schurNonpositiveWordIndex i n q x) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A (sequence A) K n).f i
        (ιTensorObj ((sequence A).level n) (TensorPowers.power K n)
          (-(q : ℤ)) (i + q) i (by omega)
          (equivariantBasis A n q (x.1, 1) ⊗ₜ[A]
            powerGradedBasis b n (i + q) x.2)) := by
  change schurDegreeBasis (sequence A) K i (schurWordPieceBasis b i)
    ⟨n, ⟨(-(q : ℤ), i + q), by omega⟩, (schurNonpositiveWordIndex i n q x).2.2⟩ = _
  rw [schurDegreeBasis_apply, schurWordPieceBasis_nonpositive,
    schurNonpositiveBidegreeBasis_eq_mk, schurBidegree_inclusion_inv]

/-- Normalization retains the specified input word. -/
@[simp]
lemma schurWordInputs_nonpositive {I : ℤ → Type u} (i : ℤ) (n q : ℕ)
    (x : ULift.{u} (BasedNondegenerate n q) × powerGradedIndex I n (i + q)) :
    schurWordInputs (schurNonpositiveWordIndex i n q x) =
      powerGradedInputs n (i + q) x.2 := by
  classical
  cases q <;> simp [schurWordInputs, schurNonpositiveWordIndex]

/-- The weight of the normalized Schur vector is the total weight of its specified inputs. -/
@[simp]
lemma schurWordWeight_nonpositive {I : ℤ → Type u} (w : (Σ i, I i) → ℕ)
    (i : ℤ) (n q : ℕ)
    (x : ULift.{u} (BasedNondegenerate n q) × powerGradedIndex I n (i + q)) :
    schurWordWeight w (schurNonpositiveWordIndex i n q x) =
      powerGradedWeight w n (i + q) x.2 := by
  simp only [schurWordWeight, schurWordInputs_nonpositive, powerGradedWeight]

end BarrattEccles
end SerrePositivity.EInfinity
