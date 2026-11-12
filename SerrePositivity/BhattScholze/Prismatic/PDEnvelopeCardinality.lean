module

public import SerrePositivity.BhattScholze.Prismatic.RelativePDEnvelope
public import Mathlib.Data.W.Cardinal
import all SerrePositivity.BhattScholze.Prismatic.RelativePDEnvelope

/-!
# 相対分冪包の濃度評価

## 概要
未完備の相対分冪包の濃度は、入力環の濃度と可算濃度の最大値で抑えられる。

## 方針
有限分岐の構文木から二種類の形式項へ全射を作り、その商である包の濃度を評価する。

## 規約
分冪基底の構造は固定し、入力環の濃度だけを使う。

## 使われ方
Berthelot I.2.3.1、III.4。分冪 Čech 包の cutoff の検証。
-/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Prismatic
namespace PDEnvelopeCardinality
variable {B : Type u} [CommRing B] (K : Ideal B)

private abbrev Label := B ⊕ K ⊕ (Fin 6 × ℕ)
private def Branch : Label K → Type
  | .inl _ => Empty
  | .inr (.inl _) => Empty
  | .inr (.inr _) => Bool

private instance (a : Label K) : Finite (Branch K a) := by
  rcases a with _ | (_ | _ ) <;> dsimp only [Branch] <;> infer_instance

private abbrev Tree := WType (Branch K)
private abbrev Terms := RelativePDEnvelope.Term K false × RelativePDEnvelope.Term K true

private def operate : (Σ a : Label K, Branch K a → Terms K) → Terms K
  | ⟨.inl b, _⟩ => (.const b, .gen 0)
  | ⟨.inr (.inl b), _⟩ => (.ofIdeal (.gen b), .gen b)
  | ⟨.inr (.inr (0, _)), f⟩ => (.add (f false).1 (f true).1, .add (f false).2 (f true).2)
  | ⟨.inr (.inr (1, _)), f⟩ => (.neg (f false).1, .neg (f false).2)
  | ⟨.inr (.inr (2, _)), f⟩ => (.mul (f false).1 (f true).1, .mul (f false).1 (f true).2)
  | ⟨.inr (.inr (3, n)), f⟩ => (.pow (f false).1 n, .gen 0)
  | ⟨.inr (.inr (4, n)), f⟩ => (.ofIdeal (.dp n (f false).2), .dp n (f false).2)
  | ⟨.inr (.inr (5, _)), f⟩ => (.ofIdeal (f false).2, .gen 0)

private def interpret : Tree K → Terms K := WType.elim _ (operate K)
private def select (t : Terms K) : (i : Bool) → RelativePDEnvelope.Term K i
  | false => t.1
  | true => t.2
private def opTree (o : Fin 6) (n : ℕ) (a b : Tree K) : Tree K :=
  WType.mk (.inr (.inr (o, n))) (fun x => Bool.rec a b x)

private theorem exists_tree {i : Bool} (t : RelativePDEnvelope.Term K i) :
    ∃ w : Tree K, select K (interpret K w) i = t := by
  induction t with
  | const b => exact ⟨WType.mk (.inl b) Empty.elim, rfl⟩
  | gen b => exact ⟨WType.mk (.inr (.inl b)) Empty.elim, rfl⟩
  | ofIdeal t ih =>
    obtain ⟨a, ha⟩ := ih
    refine ⟨opTree K 5 0 a a, ?_⟩
    exact congrArg RelativePDEnvelope.Term.ofIdeal ha
  | @add i t s iht ihs =>
    obtain ⟨a, ha⟩ := iht
    obtain ⟨b, hb⟩ := ihs
    refine ⟨opTree K 0 0 a b, ?_⟩
    cases i <;> exact congrArg₂ RelativePDEnvelope.Term.add ha hb
  | @neg i t ih =>
    obtain ⟨a, ha⟩ := ih
    refine ⟨opTree K 1 0 a a, ?_⟩
    cases i <;> exact congrArg RelativePDEnvelope.Term.neg ha
  | @mul i t s iht ihs =>
    obtain ⟨a, ha⟩ := iht
    obtain ⟨b, hb⟩ := ihs
    refine ⟨opTree K 2 0 a b, ?_⟩
    cases i <;> exact congrArg₂ RelativePDEnvelope.Term.mul ha hb
  | pow t n ih =>
    obtain ⟨a, ha⟩ := ih
    exact ⟨opTree K 3 n a a, congrArg (fun x => RelativePDEnvelope.Term.pow x n) ha⟩
  | dp n t ih =>
    obtain ⟨a, ha⟩ := ih
    exact ⟨opTree K 4 n a a, congrArg (RelativePDEnvelope.Term.dp n) ha⟩

variable {k : Type u} [CommRing k] [Algebra k B] {J : Ideal k} (γ : DividedPowers J)

private def toRing (w : Tree K) : RelativePDEnvelope.Ring γ K :=
  Quotient.mk'' (select K (interpret K w) false)

private theorem toRing_surjective : Function.Surjective (toRing K γ) := by
  intro x
  obtain ⟨t, rfl⟩ := Quotient.exists_rep x
  obtain ⟨w, hw⟩ := exists_tree K t
  exact ⟨w, congrArg Quotient.mk'' hw⟩

/-- 無限濃度の上限に入力環が入れば、未完備の相対分冪包も同じ上限に入る。 -/
theorem relativePDEnvelope_cardinal_le (κ : Cardinal.{u})
    (hκ : Cardinal.aleph0 ≤ κ) (hB : Cardinal.mk B ≤ κ) :
    Cardinal.mk (RelativePDEnvelope.Ring γ K) ≤ κ := by
  have hK : Cardinal.mk K ≤ κ := (Cardinal.mk_subtype_le _).trans hB
  have hOp : Cardinal.lift.{u, 0} (Cardinal.mk (Fin 6 × ℕ)) ≤ κ :=
    (Cardinal.lift_le_aleph0.mpr Cardinal.mk_le_aleph0).trans hκ
  have hLabel : Cardinal.mk (Label K) ≤ κ := by
    simp only [Label, Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_uzero]
    exact Cardinal.add_le_of_le hκ hB (Cardinal.add_le_of_le hκ hK hOp)
  have hTree : Cardinal.mk (Tree K) ≤ κ := by
    exact (WType.cardinalMk_le_max_aleph0_of_finite' (β := Branch K)).trans
      (max_le (by simpa only [Cardinal.lift_uzero] using hLabel) hκ)
  exact (Cardinal.mk_le_of_surjective (toRing_surjective K γ)).trans hTree

end PDEnvelopeCardinality
end SerrePositivity.BhattScholze.Prismatic
