module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ForwardSegmentColumnFactorization

/-!
# 元の一列へ繋ぐ前後の区間射と表示変更

概要：前置射は始点だけ、後置射は終点だけで決まり、方向の証明と外側の範囲に依存しない。
方針：保持する端点の等式で帰納し、元の定義を回収する。
規約：同じ内部列と元の端点移送を保持する。
使われ方：内部接続列の区間合成を語の fiber の切断比較へ接続する。
-/

@[expose] public section
universe u v
noncomputable section
namespace SerrePositivity.EInfinity.Hammock.Segment
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {w : Word} {X Y : C}
  (S : Zigzag W w X Y) (p q p' q' : Fin (w.length + 1))
  (hd : ∀ k : Fin w.length, p.val ≤ k.val → k.val < q.val → w.direction k = .forward)
  (hd' : ∀ k : Fin w.length, p'.val ≤ k.val → k.val < q'.val → w.direction k = .forward)
  (i : Fin w.length) (hp : p.val ≤ i.val) (hq : i.val < q.val)
  (hp' : p'.val ≤ i.val) (hq' : i.val < q'.val)

lemma toColumn_heq (he : p = p') :
    HEq (toColumn S p q hd i hp hq) (toColumn S p' q' hd' i hp' hq') := by
  cases he
  rfl

lemma fromColumn_heq (he : q = q') :
    HEq (fromColumn S p q hd i hp hq) (fromColumn S p' q' hd' i hp' hq') := by
  cases he
  rfl

end SerrePositivity.EInfinity.Hammock.Segment
