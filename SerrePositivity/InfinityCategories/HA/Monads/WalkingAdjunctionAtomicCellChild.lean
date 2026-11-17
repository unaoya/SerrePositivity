module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionAtomicCellChildren

/-!
概要：全ての正の次数の純粋な実生成元から、非純粋な実子を同じ型で回収する。
方針：元の実最小元が最後かを判定し、二つの構成済みの実子を使う。
規約：子の始点を依存和で保持し、原子性・非退化性・非純粋性は実構成から得る。
使われ方：Riehl–Verity Definition 4.2.1、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実親子の対応。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：同じ全実関手を持つ生成元は同じ生成元。
方針：実関手の等式と証明の一意性を使う。
規約：同じ次数と両端。使われ方：Riehl–Verity §4.2の実親子の全関手の往復。 -/
lemma WalkingAdjunctionAtomicCell.ext_chain {n : ℕ} {X Y : WalkingAdjunctionPoint}
    {a b : WalkingAdjunctionAtomicCell.{u} n X Y} (h : a.chain = b.chain) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- 概要：正の次数の純粋な実生成元から、その非純粋な実子を回収する。
方針：実最小元が最後ならplus始点の実子、内側ならminus始点の実子を取る。
規約：実始点と実子を依存和で返す。使われ方：Riehl–Verity Definition 4.2.1の実子の構成。 -/
def WalkingAdjunctionAtomicCell.child {n : ℕ} {Y : WalkingAdjunctionPoint}
    (p : WalkingAdjunctionAtomicCell.{u} (n + 1) .minus Y) (hfill : p.NativeFillable) :
    Σ X : WalkingAdjunctionPoint,
      {a : WalkingAdjunctionAtomicCell.{u} n X Y // ¬ a.NativeFillable} :=
  match n, p, hfill with
  | 0, p, hfill => ⟨.plus, p.lastChild (by
      apply Fin.ext
      have h := (walkingAdjunctionFirstBottomMergeIndex p.chain
        (walkingAdjunctionAtomic_endpoint_cards p.chain p.atomic).2 p.nondegenerate).isLt
      change (walkingAdjunctionFirstBottomMergeIndex p.chain
        (walkingAdjunctionAtomic_endpoint_cards p.chain p.atomic).2 p.nondegenerate).val = 0
      omega) hfill⟩
  | n + 1, p, hfill => by
    classical
    let k := walkingAdjunctionFirstBottomMergeIndex p.chain
      (walkingAdjunctionAtomic_endpoint_cards p.chain p.atomic).2 p.nondegenerate
    exact if hk : k = Fin.last (n + 1) then ⟨.plus, p.lastChild hk hfill⟩ else
      ⟨.minus, p.innerChild (k.castPred hk) (Fin.castSucc_castPred k hk).symm hfill⟩

/-- 概要：正の次数の実子の選択は、実最小元が最後なら最後の実子に等しい。
方針：依存和の値として同じ実分岐を評価する。
規約：依存する始点を保持。使われ方：Riehl–Verity §4.2の実子の最後の分岐。 -/
lemma WalkingAdjunctionAtomicCell.child_of_last {n : ℕ} {Y : WalkingAdjunctionPoint}
    (p : WalkingAdjunctionAtomicCell.{u} (n + 2) .minus Y) (hfill : p.NativeFillable)
    (hk : walkingAdjunctionFirstBottomMergeIndex p.chain
      (walkingAdjunctionAtomic_endpoint_cards p.chain p.atomic).2 p.nondegenerate =
      Fin.last (n + 1)) : p.child hfill = ⟨.plus, p.lastChild hk hfill⟩ := by
  classical
  dsimp only [child]
  exact dite_eq_left hk

/-- 概要：実子の選択は、実最小元が最後でなければ内側の実子に等しい。
方針：依存和の値として実分岐を評価し、実添字のcastPredを保持する。
規約：依存する始点を保持。使われ方：Riehl–Verity §4.2の実子の内側の分岐。 -/
lemma WalkingAdjunctionAtomicCell.child_of_not_last {n : ℕ} {Y : WalkingAdjunctionPoint}
    (p : WalkingAdjunctionAtomicCell.{u} (n + 2) .minus Y) (hfill : p.NativeFillable)
    (hk : walkingAdjunctionFirstBottomMergeIndex p.chain
      (walkingAdjunctionAtomic_endpoint_cards p.chain p.atomic).2 p.nondegenerate ≠
      Fin.last (n + 1)) : p.child hfill =
      ⟨.minus, p.innerChild ((walkingAdjunctionFirstBottomMergeIndex p.chain
        (walkingAdjunctionAtomic_endpoint_cards p.chain p.atomic).2 p.nondegenerate).castPred hk)
        (Fin.castSucc_castPred _ hk).symm hfill⟩ := by
  classical
  dsimp only [child]
  exact dite_eq_right hk

/-- 概要：最後の実子から実親を作り直すと、元の実生成元へ戻る。
方針：構成済みの全実関手の往復を、生成元の等式へ移す。
規約：元の実最小元と純粋性からの構成。使われ方：Riehl–Verity §4.2の実親の回収。 -/
lemma WalkingAdjunctionAtomicCell.lastChild_parent {n : ℕ} {Y : WalkingAdjunctionPoint}
    (p : WalkingAdjunctionAtomicCell.{u} (n + 1) .minus Y)
    (hk : walkingAdjunctionFirstBottomMergeIndex p.chain
      (walkingAdjunctionAtomic_endpoint_cards p.chain p.atomic).2 p.nondegenerate = Fin.last n)
    (hfill : p.NativeFillable) :
    ((p.lastChild hk hfill).val.parent (p.lastChild hk hfill).property) = p := by
  apply ext_chain
  have hp : walkingAdjunctionOrdinalCard .minus Y (p.chain.obj (Fin.last n).succ) =
      walkingAdjunctionOrdinalCard .minus Y (p.chain.obj (Fin.last n).castSucc) - 2 + 1 ∧
      ∀ i, (walkingAdjunctionOrderHom (p.chain.map
        (homOfLE (Fin.castSucc_le_succ (Fin.last n)))) i).val = i.val - 1 := by
    exact p.pure_at_of_nativeFillable _ hk hfill
  exact walkingAdjunctionPlusChild_parent p.chain p.atomic p.nondegenerate hk hp

/-- 概要：内側の実子から実親を作り直すと、元の実生成元へ戻る。
方針：実指定面とその実最小元からの全実関手の往復を、生成元の等式へ移す。
規約：元の実最小元と純粋性からの構成。使われ方：Riehl–Verity §4.2の内側の実親の回収。 -/
lemma WalkingAdjunctionAtomicCell.innerChild_parent {n : ℕ} {Y : WalkingAdjunctionPoint}
    (p : WalkingAdjunctionAtomicCell.{u} (n + 2) .minus Y) (k : Fin (n + 1))
    (hk : walkingAdjunctionFirstBottomMergeIndex p.chain
      (walkingAdjunctionAtomic_endpoint_cards p.chain p.atomic).2 p.nondegenerate = k.castSucc)
    (hfill : p.NativeFillable) :
    ((p.innerChild k hk hfill).val.parent (p.innerChild k hk hfill).property) = p := by
  apply ext_chain
  have hp : walkingAdjunctionOrdinalCard .minus Y (p.chain.obj k.castSucc.succ) =
      walkingAdjunctionOrdinalCard .minus Y (p.chain.obj k.castSucc.castSucc) - 2 + 1 ∧
      ∀ i, (walkingAdjunctionOrderHom (p.chain.map
        (homOfLE (Fin.castSucc_le_succ k.castSucc))) i).val = i.val - 1 := by
    exact p.pure_at_of_nativeFillable _ hk hfill
  exact walkingAdjunctionInnerFace_firstRefinement p.chain k p.atomic p.nondegenerate hk hp

/-- 概要：回収した実子から実親を作り直すと、元の純粋な実生成元へ戻る。
方針：実最小元での同じ場合分けに沿い、最後と内側の実全関手の往復を使う。
規約：依存和の実子の始点も保持。使われ方：Riehl–Verity Definition 4.2.1の実親子の往復。 -/
lemma WalkingAdjunctionAtomicCell.child_parent {n : ℕ} {Y : WalkingAdjunctionPoint}
    (p : WalkingAdjunctionAtomicCell.{u} (n + 1) .minus Y) (hfill : p.NativeFillable) :
    ((p.child hfill).2.val.parent (p.child hfill).2.property) = p := by
  classical
  cases n with
  | zero => exact lastChild_parent p _ hfill
  | succ n =>
    let P := fun z : Σ X : WalkingAdjunctionPoint,
      {a : WalkingAdjunctionAtomicCell.{u} (n + 1) X Y // ¬ a.NativeFillable} =>
        z.2.val.parent z.2.property
    by_cases hk : walkingAdjunctionFirstBottomMergeIndex p.chain
        (walkingAdjunctionAtomic_endpoint_cards p.chain p.atomic).2 p.nondegenerate =
        Fin.last (n + 1)
    · exact (congrArg P (p.child_of_last hfill hk)).trans (lastChild_parent p hk hfill)
    · exact (congrArg P (p.child_of_not_last hfill hk)).trans
        (innerChild_parent p _ (Fin.castSucc_castPred
          (walkingAdjunctionFirstBottomMergeIndex p.chain
            (walkingAdjunctionAtomic_endpoint_cards p.chain p.atomic).2 p.nondegenerate) hk).symm
          hfill)

end SerrePositivity.InfinityCategories.HA.Monads
