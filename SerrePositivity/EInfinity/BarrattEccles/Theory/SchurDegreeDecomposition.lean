module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.ArityCoinvariantColimit
public import SerrePositivity.EInfinity.BarrattEccles.Theory.TensorDegreeRepresentation

/-!
# Schur 複体の arity と双次数による分解

## 概要
Berger–Moerdijk §1 の Schur 関手の次数成分を、対角作用の余不変の余積で表示する。

## 方針
有限全単射上の余極限を arity ごとに分け、各 arity のテンソルを双次数で分ける。

## 規約
零入力の arity と全ての整数双次数を含む。

## 使われ方
セル代数の次数付き自由表示から、台の次数ごとの基底を取り出す。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory Limits MonoidalCategory HomologicalComplex DifferentialGraded

variable {A : Type u} [CommRing A]

/-- The group action at the standard object of a diagram of complexes. -/
def finiteBijectionComplexAction (F : FiniteBijection ⥤ Complex A) (n : ℕ) :
    ULift.{u} (Equiv.Perm (Fin n)) →* End (F.obj (FiniteBijection.of n)) where
  toFun σ := .of (F.map (FiniteBijection.permutation n σ.down))
  map_one' := by
    apply End.ext
    change F.map (FiniteBijection.permutation n 1) = 𝟙 _
    rw [FiniteBijection.permutation_one, F.map_id]
  map_mul' σ τ := by
    apply End.ext
    change F.map (FiniteBijection.permutation n (σ.down * τ.down)) = _
    rw [FiniteBijection.permutation_mul, F.map_comp]
    rfl

/-- The bidegree representation for the tensor in one arity of the Schur diagram. -/
def schurArityBidegreeRepresentation (P : SymmetricSequence (Complex A)) (K : Complex A)
    (i : ℤ) (n : ℕ) (a : {a : ℤ × ℤ // a.1 + a.2 = i}) :
    Rep.{u} A (ULift.{u} (Equiv.Perm (Fin n))) :=
  tensorDegreeRepresentationSummand (finiteBijectionComplexAction P n)
    (finiteBijectionComplexAction (TensorPowers.bijectionFunctor K) n) i a

/-- The arity coinvariant in a Schur degree is the coproduct of its bidegree coinvariants. -/
def schurArityDegreeBidegreeIso (P : SymmetricSequence (Complex A)) (K : Complex A)
    (i : ℤ) (n : ℕ) :
    arityDiagramCoinvariants
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K ⋙ HomologicalComplex.eval (ModuleCat A) (.up ℤ) i) n ≅
      ∐ (fun a => ModuleCat.of A (schurArityBidegreeRepresentation P K i n a).ρ.Coinvariants) :=
  tensorDegreeCoinvariantsIso (finiteBijectionComplexAction P n)
    (finiteBijectionComplexAction (TensorPowers.bijectionFunctor K) n) i

/-- The actual Schur degree decomposes into arity and bidegree coinvariants. -/
def schurDegreeBidegreeIso (P : SymmetricSequence (Complex A)) (K : Complex A) (i : ℤ) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P).obj K).X i ≅
      ∐ (fun n : ℕ => ∐ (fun a =>
        ModuleCat.of A (schurArityBidegreeRepresentation P K i n a).ρ.Coinvariants)) :=
  schurDegreeArityIso P K i ≪≫ Sigma.mapIso (schurArityDegreeBidegreeIso P K i)

end SerrePositivity.EInfinity
