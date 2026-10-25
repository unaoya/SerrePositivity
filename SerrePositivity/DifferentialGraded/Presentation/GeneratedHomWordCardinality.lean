module
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHomWords
public import Mathlib.Data.W.Cardinal
/-!
概要：係数の有限語の個数は、指定生成子・対象ラベルと可算集合の最大で抑えられる。
方針：単位・生成子・微分・合成の有限分岐 W 型へ忠実に符号化する。
規約：環の元の個数を上界に含めず、線形 span の生成元数を評価する。
使われ方：c′ の係数閉包を κ 個の固定基底で被覆するための語の小ささ。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.DifferentialGraded
variable {I J : Type u} (source target : I → J) (degree : I → ℤ)

inductive DGGeneratedHomSymbol (I J : Type u)
  | unit (x : J)
  | generator (i : I)
  | derivative
  | composition

namespace DGGeneratedHomSymbol

def arity : DGGeneratedHomSymbol I J → Type u
  | .unit _ => ULift (Fin 0)
  | .generator _ => ULift (Fin 0)
  | .derivative => ULift (Fin 1)
  | .composition => ULift (Fin 2)

instance finite_arity (s : DGGeneratedHomSymbol I J) : Finite s.arity := by
  cases s <;> dsimp [arity] <;> infer_instance

def toSum : DGGeneratedHomSymbol I J → J ⊕ I ⊕ ULift.{u} Bool
  | .unit x => .inl x
  | .generator i => .inr (.inl i)
  | .derivative => .inr (.inr (ULift.up false))
  | .composition => .inr (.inr (ULift.up true))

lemma toSum_injective : Function.Injective (toSum (I := I) (J := J)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [toSum]

end DGGeneratedHomSymbol
namespace DGGeneratedHomWord

def encode {x y : J} {n : ℤ} (a : DGGeneratedHomWord source target degree x y n) :
    WType (DGGeneratedHomSymbol.arity (I := I) (J := J)) :=
  match a with
  | .unit x => .mk (.unit x) (fun i => Fin.elim0 i.down)
  | .generator i => .mk (.generator i) (fun j => Fin.elim0 j.down)
  | .derivative a => .mk .derivative (fun _ => encode a)
  | .composition a b => .mk .composition (fun i => if i.down = 0 then encode a else encode b)

lemma encode_heq {x y x' y' : J} {n n' : ℤ}
    (a : DGGeneratedHomWord source target degree x y n)
    (other : DGGeneratedHomWord source target degree x' y' n')
    (h : encode source target degree a = encode source target degree other) : x = x' ∧ y = y' ∧ n = n' ∧ HEq a other := by
  induction a generalizing x' y' n' with
  | unit x =>
    cases other <;> simp_all [encode, WType.mk.injEq]
    obtain ⟨rfl, _⟩ := h
    exact HEq.rfl
  | generator i =>
    cases other <;> simp_all [encode, WType.mk.injEq]
    obtain ⟨rfl, _⟩ := h
    exact HEq.rfl
  | derivative a ih =>
    cases other <;> simp only [encode, WType.mk.injEq, reduceCtorEq,
      false_and, and_false, true_and] at h
    have hf := h
    have he := congrFun (eq_of_heq hf) (ULift.up (0 : Fin 1))
    obtain ⟨rfl, rfl, rfl, hh⟩ := ih _ he
    cases eq_of_heq hh
    exact ⟨rfl, rfl, rfl, HEq.rfl⟩
  | composition a b iha ihb =>
    cases other <;> simp only [encode, WType.mk.injEq, reduceCtorEq,
      false_and, and_false, true_and] at h
    have hf := h
    have h₀ := congrFun (eq_of_heq hf) (ULift.up (0 : Fin 2))
    have h₁ := congrFun (eq_of_heq hf) (ULift.up (1 : Fin 2))
    simp at h₀ h₁
    obtain ⟨rfl, rfl, rfl, ha⟩ := iha _ h₀
    obtain ⟨_, rfl, rfl, hb⟩ := ihb _ h₁
    cases eq_of_heq ha
    cases eq_of_heq hb
    exact ⟨rfl, rfl, rfl, HEq.rfl⟩

lemma encode_injective (x y : J) (n : ℤ) :
    Function.Injective (encode source target degree (x := x) (y := y) (n := n)) :=
  fun a b h => eq_of_heq (encode_heq source target degree a b h).2.2.2

lemma cardinalMk_le (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (hI : Cardinal.mk I ≤ κ) (hJ : Cardinal.mk J ≤ κ) (x y : J) (n : ℤ) :
    Cardinal.mk (DGGeneratedHomWord source target degree x y n) ≤ κ := by
  apply (Cardinal.mk_le_of_injective (encode_injective source target degree x y n)).trans
  apply WType.cardinalMk_le_max_aleph0_of_finite.trans
  apply max_le _ hκ
  apply (Cardinal.mk_le_of_injective (DGGeneratedHomSymbol.toSum_injective
    (I := I) (J := J))).trans
  simp only [Cardinal.mk_sum, Cardinal.lift_id]
  exact Cardinal.add_le_of_le hκ hJ (Cardinal.add_le_of_le hκ hI
    (Cardinal.mk_le_aleph0.trans hκ))

end DGGeneratedHomWord
end SerrePositivity.DifferentialGraded
