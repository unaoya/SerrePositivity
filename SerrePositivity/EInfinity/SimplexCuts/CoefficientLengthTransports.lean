module

public import SerrePositivity.EInfinity.SimplexCuts.CoefficientDifferentialValues

/-!
# 同じ係数語の語長の等式移送

Berger–Fresse §1.2.3・§2.2.7、M14 L09の証明分割。
既存の語・文字削除・削除係数・有効性・実生成元を同じ語長の等式で運ぶ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open scoped Simplicial

/-- C286：同じ語長の等式移送は、その値の有限添字の等式移送。 -/
lemma word_cast_val {r ℓ ℓ' : ℕ} (h : ℓ = ℓ') (v : Surjection.Word r ℓ) :
    (Eq.mp (congrArg (Surjection.Word r) h) v).val =
      fun i : Fin ℓ' => v.val (Fin.cast h.symm i) := by
  subst ℓ'
  rfl

/-- C287：同じ語長と指定位置の等式移送は、既存の削除係数を保つ。 -/
lemma deletionCoefficient_cast_length {r ℓ ℓ' : ℕ} (h : ℓ = ℓ')
    (v : Fin ℓ → Fin r) (a : Fin ℓ) :
    Surjection.deletionCoefficient (fun i : Fin ℓ' => v (Fin.cast h.symm i)) (Fin.cast h a) =
      Surjection.deletionCoefficient v a := by
  subst ℓ'
  rfl

/-- C288：同じ語長と指定位置の等式移送は、既存の文字削除と可換。 -/
lemma erase_cast_length {r ℓ ℓ' : ℕ} (h : ℓ = ℓ')
    (v : Fin (ℓ + 1) → Fin r) (a : Fin (ℓ + 1)) :
    Surjection.erase
        (fun i : Fin (ℓ' + 1) => v (Fin.cast (congrArg (fun n : ℕ => n + 1) h.symm) i))
        (Fin.cast (congrArg (fun n : ℕ => n + 1) h) a) =
      fun i : Fin ℓ' => Surjection.erase v a (Fin.cast h.symm i) := by
  subst ℓ'
  rfl

/-- C289：同じ語長の等式移送は、既存の有効な語の判定を保つ。 -/
lemma word_valid_cast_length {r ℓ ℓ' : ℕ} (h : ℓ = ℓ') (v : Fin ℓ → Fin r) :
    (Function.Surjective v ∧ Surjection.Nondegenerate v) ↔
      (Function.Surjective (fun i : Fin ℓ' => v (Fin.cast h.symm i)) ∧
        Surjection.Nondegenerate (fun i : Fin ℓ' => v (Fin.cast h.symm i))) := by
  subst ℓ'
  rfl

/-- C290：元の係数加群の自然な語長へ移した同じ生成元の評価。 -/
lemma rawComponent_generator_cast_length (A : Type u) [CommRing A] (S : SSet.{0})
    {r d q ℓ : ℕ} (h : ℓ = (r + 1) + d) (v : Fin ℓ → Fin (r + 1)) (x : S _⦋q⦌) :
    rawComponent A S r d q
        (Surjection.generator A (fun i : Fin ((r + 1) + d) => v (Fin.cast h.symm i)))
        (ModuleCat.freeMk (ULift.up x)) =
      if hv : Function.Surjective v ∧ Surjection.Nondegenerate v then
        cutSum A S (Eq.mp (congrArg (Surjection.Word (r + 1)) h) ⟨v, hv⟩) x
      else 0 := by
  subst ℓ
  convert rawComponent_generator A S v x using 1
  all_goals rfl

end SerrePositivity.EInfinity.SimplexCuts
