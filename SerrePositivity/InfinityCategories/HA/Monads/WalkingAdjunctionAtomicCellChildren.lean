module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionAtomicCells
public import
  SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionInnerParentReconstruction

/-!
概要：純粋な実親から、最後の場合と内側の場合の非純粋な実子を生成元の型で回収する。
方針：構成済みの実子の原子性・非退化性・実最小元・非純粋性を同じ型へ移す。
規約：子の存在や非純粋性を新しく入力しない。
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

/-- 概要：実最小元の等式で、模型の純粋性を指定した同じ実添字へ移す。
方針：実添字を同一視し、定義された全点の条件を回収する。
規約：依存する有限点の型も同じ実添字。使われ方：Riehl–Verity §4.2の実子への輸送。 -/
lemma WalkingAdjunctionAtomicCell.pure_at_of_nativeFillable {n : ℕ}
    {Y : WalkingAdjunctionPoint} (p : WalkingAdjunctionAtomicCell.{u} (n + 1) .minus Y)
    (k : Fin (n + 1))
    (hk : walkingAdjunctionFirstBottomMergeIndex p.chain
      (walkingAdjunctionAtomic_endpoint_cards p.chain p.atomic).2 p.nondegenerate = k)
    (hfill : p.NativeFillable) :
    walkingAdjunctionOrdinalCard .minus Y (p.chain.obj k.succ) =
        walkingAdjunctionOrdinalCard .minus Y (p.chain.obj k.castSucc) - 2 + 1 ∧
      ∀ i, (walkingAdjunctionOrderHom (p.chain.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = i.val - 1 := by
  subst k
  exact hfill

/-- 概要：最初の純粋な実併合が最後の実親から、plus始点の非純粋な実子を回収する。
方針：構成済みの最後の面の前置を除く実子と、その原子性・非退化性を使う。
規約：同じ実親からの実データ。使われ方：Riehl–Verity §4.2の最後の深さの実子。 -/
def WalkingAdjunctionAtomicCell.lastChild {n : ℕ} {Y : WalkingAdjunctionPoint}
    (p : WalkingAdjunctionAtomicCell.{u} (n + 1) .minus Y)
    (hk : walkingAdjunctionFirstBottomMergeIndex p.chain
      (walkingAdjunctionAtomic_endpoint_cards p.chain p.atomic).2 p.nondegenerate = Fin.last n)
    (hfill : p.NativeFillable) :
    {a : WalkingAdjunctionAtomicCell.{u} n .plus Y // ¬ a.NativeFillable} := by
  have hp : walkingAdjunctionOrdinalCard .minus Y (p.chain.obj (Fin.last n).succ) =
      walkingAdjunctionOrdinalCard .minus Y (p.chain.obj (Fin.last n).castSucc) - 2 + 1 ∧
      ∀ i, (walkingAdjunctionOrderHom (p.chain.map
        (homOfLE (Fin.castSucc_le_succ (Fin.last n)))) i).val = i.val - 1 := by
    exact p.pure_at_of_nativeFillable _ hk hfill
  exact ⟨⟨walkingAdjunctionPlusChild p.chain p.atomic p.nondegenerate hk hp,
    walkingAdjunctionPlusChild_atomic p.chain p.atomic p.nondegenerate hk hp,
    walkingAdjunctionPlusChild_nondegenerate p.chain p.atomic p.nondegenerate hk hp⟩,
    fun h => h⟩

/-- 概要：最初の純粋な実併合が内側の実親から、minus始点の非純粋な実子を回収する。
方針：実指定面の原子性・非退化性・実最小元を回収し、純粋な実親の逆の法則を使う。
規約：実子の非純粋性は結論に保持。使われ方：Riehl–Verity §4.2の内側の実親子の対応。 -/
def WalkingAdjunctionAtomicCell.innerChild {n : ℕ} {Y : WalkingAdjunctionPoint}
    (p : WalkingAdjunctionAtomicCell.{u} (n + 2) .minus Y) (k : Fin (n + 1))
    (hk : walkingAdjunctionFirstBottomMergeIndex p.chain
      (walkingAdjunctionAtomic_endpoint_cards p.chain p.atomic).2 p.nondegenerate = k.castSucc)
    (hfill : p.NativeFillable) :
    {a : WalkingAdjunctionAtomicCell.{u} (n + 1) .minus Y // ¬ a.NativeFillable} := by
  have hp : walkingAdjunctionOrdinalCard .minus Y (p.chain.obj k.castSucc.succ) =
      walkingAdjunctionOrdinalCard .minus Y (p.chain.obj k.castSucc.castSucc) - 2 + 1 ∧
      ∀ i, (walkingAdjunctionOrderHom (p.chain.map
        (homOfLE (Fin.castSucc_le_succ k.castSucc))) i).val = i.val - 1 := by
    exact p.pure_at_of_nativeFillable _ hk hfill
  have hm := walkingAdjunctionInnerFace_first_merge p.chain k p.atomic p.nondegenerate hk
  let H := finiteChainFace p.chain k.succ.castSucc
  let ha := walkingAdjunctionInnerFace_atomic p.chain k p.atomic
  let hn := walkingAdjunctionInnerFace_nondegenerate p.chain k p.nondegenerate hm
  refine ⟨⟨H, ha, hn⟩, ?_⟩
  change ¬ (
    let j := walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hn
    walkingAdjunctionOrdinalCard .minus Y (H.obj j.succ) =
        walkingAdjunctionOrdinalCard .minus Y (H.obj j.castSucc) - 2 + 1 ∧
      ∀ i, (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ j))) i).val = i.val - 1)
  dsimp only
  rw [walkingAdjunctionInnerFace_first_index p.chain k p.atomic p.nondegenerate hk]
  intro h
  have hs := congrArg (walkingAdjunctionOrdinalCard .minus Y)
    (finiteChainFace_inner_before_obj p.chain k k.castSucc le_rfl)
  have hpure := walkingAdjunctionInnerFace_not_pure p.chain k hm p.nondegenerate hp
  apply hpure
  refine ⟨?_, h.2⟩
  have hc := h.1
  change walkingAdjunctionOrdinalCard .minus Y (H.obj k.succ) =
    walkingAdjunctionOrdinalCard .minus Y (p.chain.obj k.castSucc.castSucc) - 2 + 1
  change walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) =
    walkingAdjunctionOrdinalCard .minus Y (p.chain.obj k.castSucc.castSucc) at hs
  omega

end SerrePositivity.InfinityCategories.HA.Monads
