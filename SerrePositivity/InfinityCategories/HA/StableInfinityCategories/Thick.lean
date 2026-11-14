module

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure
public import Mathlib.CategoryTheory.Retract

/-!
# 安定準圏の厚い頂点条件

概要：HA §1.1.3 の安定な充満部分圏に、HTT §4.4.5 の retract 閉性を加える。
方針：零・同型・実 cofiber/fiber・ホモトピー圏の retract に対する閉性で定義する。
規約：対象の有限な安定閉包と retract 閉包を区別し、テンソル構造は要求しない。
使われ方：安定圏の厚い核、厚いテンソルイデアルの共通の芯。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open scoped Simplicial

/-- 概要：安定準圏の厚い充満部分圏を定める頂点条件（HA §1.1.3、HTT §4.4.5）。
方針：実安定閉性とホモトピー圏での retract 閉性を指定する。
規約：retract の二射の合成は恒等射。テンソルは含まない。
使われ方：厚い閉包と厚いテンソルイデアルに共通の定義。 -/
structure IsThick (C : SSet.{u}) [Quasicategory C] [IsStable C]
    (P : C _⦋0⦌ → Prop) : Prop where
  /-- 零対象を含む（HA §1.1.3）。 -/
  zero {x} : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex x → P x
  /-- 同型で閉じる（HA §1.1.3）。 -/
  iso {x y} : VertexIso x y → P x → P y
  /-- 実 cofiber 列の始域と中間項から終域へ閉じる（HA §1.1.3）。 -/
  cofiber (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle C) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence t →
    P (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 0 0) → P (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 1 0) →
      P (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 1 1)
  /-- 実 fiber 列の中間項と終域から始域へ閉じる（HA §1.1.3）。 -/
  fiber (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle C) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsFiberSequence t →
    P (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 1 0) → P (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 1 1) →
      P (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 0 0)
  /-- ホモトピー圏での retract に閉じる（HTT §4.4.5）。 -/
  retract {x y} : Nonempty (Retract (HomotopyCategory.mk x) (HomotopyCategory.mk y)) →
    P y → P x

variable (C : SSet.{u}) [Quasicategory C] [IsStable C]

/-- 概要：指定した頂点条件の最小の厚い閉包（HA §1.1.3、HTT §4.4.5）。
方針：全ての厚い上界の交わりを取る。
規約：retract を含む。使われ方：生成される厚い部分圏。 -/
def thickClosure (P : C _⦋0⦌ → Prop) : C _⦋0⦌ → Prop :=
  fun x => ∀ Q, IsThick C Q → (∀ y, P y → Q y) → Q x

/-- 概要：厚い閉包は元の条件を含む（HA §1.1.3、HTT §4.4.5）。
方針：任意の上界への包含を評価。規約：頂点ごとの包含。
使われ方：生成元の所属。 -/
lemma subset_thickClosure (P : C _⦋0⦌ → Prop) {x} (hx : P x) : thickClosure C P x :=
  fun _ _ h => h x hx

/-- 概要：厚い閉包自体が厚い（HA §1.1.3、HTT §4.4.5）。
方針：各閉性を全ての厚い上界で確認する。
規約：実 cofiber/fiber と元の retract を保つ。使われ方：閉包の普遍性。 -/
lemma thickClosure_isThick (P : C _⦋0⦌ → Prop) : IsThick C (thickClosure C P) where
  zero h Q hQ _ := hQ.zero h
  iso e hx Q hQ hP := hQ.iso e (hx Q hQ hP)
  cofiber t ht hx hy Q hQ hP := hQ.cofiber t ht (hx Q hQ hP) (hy Q hQ hP)
  fiber t ht hx hy Q hQ hP := hQ.fiber t ht (hx Q hQ hP) (hy Q hQ hP)
  retract r hy Q hQ hP := hQ.retract r (hy Q hQ hP)

/-- 概要：厚い上界への包含は生成元で判定できる（HA §1.1.3、HTT §4.4.5）。
方針：交わりの定義と生成元の包含を往復する。
規約：Q の厚さを明示。使われ方：厚い閉包の最小性。 -/
lemma thickClosure_le_iff (P Q : C _⦋0⦌ → Prop) (hQ : IsThick C Q) :
    (∀ x, thickClosure C P x → Q x) ↔ ∀ x, P x → Q x := by
  constructor
  · intro h x hx
    exact h x (subset_thickClosure C P hx)
  · intro h x hx
    exact hx Q hQ h

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
