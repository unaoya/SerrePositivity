module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionSum

/-!
模型。文献の定義との比較は後で
# Schedule ごとの成功削除点の fiber

概要：Berger–Fresse §1.4.4 の全成功削除点の和を元の Schedule の和へ戻す。
方針：成功する Schedule の fiber を出力位置の有限型と同定する。
規約：抽出失敗の Schedule の fiber は空。
使われ方：remainderTerm の和と全成功削除点上の残余和を照合する。
-/

@[expose] public section

noncomputable section

universe u


namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：同じ Schedule の成功出力は一致（BF §1.4.4）。
方針：reduceRows の二つの成功等式を比較する。
規約：出力の正規化は使わない。
使われ方：削除点の位置を指定出力の有限添字へ移す。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint.output_eq {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)}
    (p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint w) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (out : List (Fin n))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out) (hs : p.schedule = r) : p.output = out := by
  have hp := p.success
  rw [hs] at hp
  exact Option.some.inj (hp.symm.trans h)

/-- 概要：成功 Schedule 上の削除点の fiber は実際の出力位置と全単射（BF §1.4.4）。
方針：成功出力の一意性で添字を移し、元の成功から逆の削除点を構成する。
規約：出力位置は全て含む。
使われ方：Schedule ごとの有限和を元の位置和へ付け替える。 -/
def deletionFiberEquiv {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (out : List (Fin n)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out) :
    {p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint w // p.schedule = r} ≃ Fin out.length where
  toFun p := ⟨p.val.position.val, by
    have hl := congrArg List.length (p.val.output_eq r out h p.property)
    have := p.val.position.isLt
    omega⟩
  invFun k := ⟨⟨r, out, h, k⟩, rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint.ext _ _ p.property.symm
    rfl
  right_inv k := Fin.ext rfl

open _root_.Classical in
/-- 概要：成功 Schedule の fiber 上の残余和は元の残余位置和（BF §1.4.4）。
方針：出力位置との全単射で和を付け替え、定義を照合する。
規約：削除後次数は d。
使われ方：remainderTerm の成功分岐を全成功削除点の和へ移す。 -/
lemma sum_fiber_remainingValue (A : Type u) [CommRing A] {n d : ℕ}
    (w : Fin (d + 2) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n (d + 1))
    (out : List (Fin n)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out) :
    (∑ p : {p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint w // p.schedule = r}, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.remainingValue A p.val) =
      ∑ k : Fin out.length, if k ∉ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.singletonPositions r out (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_length w r out h) then
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listDeletionTerm A out k else 0 := by
  classical
  apply Fintype.sum_equiv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionFiberEquiv w r out h)
  intro p
  rcases p with ⟨⟨r', out', h', k⟩, hs⟩
  dsimp only at hs
  subst r'
  have ho : out' = out := Option.some.inj (h'.symm.trans h)
  subst out'
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.remainingValue, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint.Remaining, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionValue, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionFiberEquiv,
    Equiv.coe_fn_mk]
  apply ite_congr rfl <;> intro _ <;> rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
