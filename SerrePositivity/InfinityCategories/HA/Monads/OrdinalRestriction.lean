module

public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalConcatenation

/-!
概要：有限単調射を、指定した区間の間の実単調射へ制限する。
方針：区間への包含で評価して始点のずれを引き、像の上下の条件を使う。
規約：区間の像に入る条件は全点で明示する。
使われ方：Riehl–Verity Proposition 3.1.10・Remark 3.3.8、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の残りの水平因子の射。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：指定した有限区間の全体への包含。
方針：始点のずれを加える。規約：空の区間も許す。
使われ方：Riehl–Verity Proposition 3.1.10 の切れ目の間の部分。 -/
def ordinalSegmentInclusion (m a r : ℕ) (h : a + r ≤ m) : Fin r →o Fin m where
  toFun i := ⟨a + i.val, by have := i.isLt; omega⟩
  monotone' := by
    intro i j hij
    change a + i.val ≤ a + j.val
    exact Nat.add_le_add_left hij a

/-- 概要：像の上下の条件を持つ有限単調射の実区間制限。
方針：元の像の値から値域の始点を引く。
規約：元の射と二つの区間を保持する。使われ方：Riehl–Verity Proposition 3.1.10。 -/
def ordinalRestrict {m n : ℕ} (f : Fin m →o Fin n) (a c r s : ℕ) (ha : a + r ≤ m)
    (hl : ∀ i, c ≤ (f (ordinalSegmentInclusion m a r ha i)).val)
    (hu : ∀ i, (f (ordinalSegmentInclusion m a r ha i)).val < c + s) : Fin r →o Fin s where
  toFun i := ⟨(f (ordinalSegmentInclusion m a r ha i)).val - c, by
    have h₁ := hl i
    have h₂ := hu i
    omega⟩
  monotone' := by
    intro i j hij
    exact Nat.sub_le_sub_right (f.monotone ((ordinalSegmentInclusion m a r ha).monotone hij)) c

/-- 概要：区間へ制限した射の自然数の値。
方針：構成の定義。規約：始点のずれの引算を明記する。
使われ方：Riehl–Verity Proposition 3.1.10 の全射の照合。 -/
lemma ordinalRestrict_val {m n : ℕ} (f : Fin m →o Fin n) (a c r s : ℕ) (ha : a + r ≤ m)
    (hl : ∀ i, c ≤ (f (ordinalSegmentInclusion m a r ha i)).val)
    (hu : ∀ i, (f (ordinalSegmentInclusion m a r ha i)).val < c + s) (i : Fin r) :
    (ordinalRestrict f a c r s ha hl hu i).val =
      (f (ordinalSegmentInclusion m a r ha i)).val - c := rfl

/-- 概要：区間への包含を通せば制限した射は元の射と可換する。
方針：像の下限と加法・減法の相殺を使う。
規約：値域の区間も全体に入る条件を明示する。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma ordinalRestrict_square {m n : ℕ} (f : Fin m →o Fin n) (a c r s : ℕ)
    (ha : a + r ≤ m) (hc : c + s ≤ n)
    (hl : ∀ i, c ≤ (f (ordinalSegmentInclusion m a r ha i)).val)
    (hu : ∀ i, (f (ordinalSegmentInclusion m a r ha i)).val < c + s) :
    (ordinalSegmentInclusion n c s hc).comp (ordinalRestrict f a c r s ha hl hu) =
      f.comp (ordinalSegmentInclusion m a r ha) := by
  apply OrderHom.ext
  funext i
  apply Fin.ext
  change c + ((f (ordinalSegmentInclusion m a r ha i)).val - c) =
    (f (ordinalSegmentInclusion m a r ha i)).val
  have hi := hl i
  omega

/-- 概要：恒等射の同じ区間への制限は恒等射。
方針：始点の加法・減法を相殺する。規約：上下の条件の証明には依存しない。
使われ方：Riehl–Verity Proposition 3.1.10 の実因子の恒等射の保存。 -/
lemma ordinalRestrict_id {m a r : ℕ} (ha : a + r ≤ m)
    (hl : ∀ i, a ≤ ((OrderHom.id : Fin m →o Fin m)
      (ordinalSegmentInclusion m a r ha i)).val)
    (hu : ∀ i, ((OrderHom.id : Fin m →o Fin m)
      (ordinalSegmentInclusion m a r ha i)).val < a + r) :
    ordinalRestrict OrderHom.id a a r r ha hl hu = OrderHom.id := by
  apply OrderHom.ext
  funext i
  apply Fin.ext
  change a + i.val - a = i.val
  omega

/-- 概要：二つの射の区間への制限は合成と両立する。
方針：最初の射の包含との可換条件を使い、二番目の射の同じ点で照合する。
規約：三つの区間と全ての像の上下の条件を明示する。
使われ方：Riehl–Verity Proposition 3.1.10 の実因子の全合成則。 -/
lemma ordinalRestrict_comp {m n k a c d r s t : ℕ} (f : Fin m →o Fin n) (g : Fin n →o Fin k)
    (ha : a + r ≤ m) (hc : c + s ≤ n)
    (hlf : ∀ i, c ≤ (f (ordinalSegmentInclusion m a r ha i)).val)
    (huf : ∀ i, (f (ordinalSegmentInclusion m a r ha i)).val < c + s)
    (hlg : ∀ i, d ≤ (g (ordinalSegmentInclusion n c s hc i)).val)
    (hug : ∀ i, (g (ordinalSegmentInclusion n c s hc i)).val < d + t)
    (hl : ∀ i, d ≤ ((g.comp f) (ordinalSegmentInclusion m a r ha i)).val)
    (hu : ∀ i, ((g.comp f) (ordinalSegmentInclusion m a r ha i)).val < d + t) :
    ordinalRestrict (g.comp f) a d r t ha hl hu =
      (ordinalRestrict g c d s t hc hlg hug).comp (ordinalRestrict f a c r s ha hlf huf) := by
  apply OrderHom.ext
  funext i
  apply Fin.ext
  have hi := congrArg (fun h : Fin r →o Fin n => h i)
    (ordinalRestrict_square f a c r s ha hc hlf huf)
  change (g (f (ordinalSegmentInclusion m a r ha i))).val - d =
    (g (ordinalSegmentInclusion n c s hc (ordinalRestrict f a c r s ha hlf huf i))).val - d
  change ordinalSegmentInclusion n c s hc (ordinalRestrict f a c r s ha hlf huf i) =
    f (ordinalSegmentInclusion m a r ha i) at hi
  rw [hi]

end SerrePositivity.InfinityCategories.HA.Monads
