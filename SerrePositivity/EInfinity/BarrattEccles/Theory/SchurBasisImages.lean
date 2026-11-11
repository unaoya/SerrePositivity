module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.SchurWordBasis

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

end BarrattEccles
end SerrePositivity.EInfinity
