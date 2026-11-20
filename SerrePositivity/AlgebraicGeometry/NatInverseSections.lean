module

public meta import SerrePositivity.Util.DeprecatedAlias
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
概要：KST §5、Stacks 0597, Lemma 10.86.3 の自然数添字の非空 Mittag–Leffler 逆系の整合的元。
方針：全射な後続写像を再帰的に持ち上げ、eventual ranges への制限で一般の場合へ移す。
規約：各段階の有限性は要求せず、添字は ℕᵒᵖ に固定する。
使われ方：有限自由列から全射への各段階の持ち上げを一つの整合的な族にする。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.FunctorToTypes

/--
概要：後続写像が全射で初段が非空な自然数逆系には整合的な元の族が存在する。
方針：初段の元を再帰的に持ち上げ、定数一点関手からの自然変換にまとめる。
規約：KST §5、Stacks 0597, Lemma 10.86.3、各段階の有限性は不要。
使われ方：Mittag–Leffler 逆系の eventual ranges への適用。
-/
theorem nonempty_sections_of_surjective_nat_inverse_system
    (F : ℕᵒᵖ ⥤ Type u) [Nonempty (F.obj (Opposite.op 0))]
    (hF : ∀ n : ℕ, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op)) :
    F.sections.Nonempty := by
  classical
  let x : ∀ n : ℕ, F.obj (Opposite.op n) :=
    Nat.rec (Classical.choice (inferInstance : Nonempty (F.obj (Opposite.op 0))))
      (fun n y => (hF n y).choose)
  have hx (n : ℕ) : F.map (homOfLE (Nat.le_succ n)).op (x (n + 1)) = x n :=
    (hF n (x n)).choose_spec
  let t : (Functor.const ℕᵒᵖ).obj PUnit.{u + 1} ⟶ F :=
    NatTrans.ofOpSequence (fun n => ↾(fun _ => x n)) (fun n => by
      ext z
      exact (hx n).symm)
  refine ⟨fun j => t.app j PUnit.unit, ?_⟩
  intro j k f
  exact (congrArg (fun g : PUnit.{u + 1} ⟶ F.obj k => g PUnit.unit) (t.naturality f)).symm

/--
概要：各段階が非空な自然数 Mittag–Leffler 逆系には整合的な元の族が存在する。
方針：eventual ranges に制限して後続写像を全射とし、得た section を標準同値で戻す。
規約：KST §5、Stacks 0597, Lemma 10.86.3 の ℕᵒᵖ の特殊形。
使われ方：全射への有限自由段階ごとの持ち上げを整合的に選ぶ。
-/
theorem nonempty_sections_of_mittagLeffler_nat_inverse_system
    (F : ℕᵒᵖ ⥤ Type u) [∀ j, Nonempty (F.obj j)] (hF : F.IsMittagLeffler) :
    F.sections.Nonempty := by
  let (j : ℕᵒᵖ) : Nonempty (F.toEventualRanges.obj j) := F.toEventualRanges_nonempty hF j
  obtain ⟨x, hx⟩ := nonempty_sections_of_surjective_nat_inverse_system F.toEventualRanges
    (fun n => F.surjective_toEventualRanges hF (homOfLE (Nat.le_succ n)).op)
  let s := F.toEventualRangesSectionsEquiv ⟨x, hx⟩
  exact ⟨s.val, s.property⟩

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
