module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionAnodyne
public import SerrePositivity.KST.Comparison.HornRightColimit
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExInfinity
public import SerrePositivity.HomotopicalAlgebra.Diagram.ColimitWeakEquivalence
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Ex∞ の Kan fibration 保存

概要：構成した有限極限を保つ Kan 置換 Ex∞ は、任意の Kan fibration を保つ。
方針：細分された horn の anodyne 性で有限反復の保存を示し、horn の有限表示可能性で余極限へ移す。
規約：Moss arXiv:1506.04887v2 Proposition 3.12。基底の Kan 性は仮定しない。
使われ方：非 Kan 基底の引き戻し比較を、Kan な基底の既証の結果へ移す。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open _root_.SerrePositivity.KST.Comparison
open CategoryTheory Limits

/--
概要：Ex の各有限反復は Kan fibration を保つ。
方針：反復回数の帰納法で一回の Ex の保存を適用する。
規約：反復の零段階は恒等関手。
使われ方：Ex∞ の arrow の順序列の各段階の Kan 条件。
-/
@[kerodon 00Z4]
theorem exIterate_map_rlp (n : ℕ) {E B : SSet.{u}} (p : E ⟶ B)
    (hp : SSet.modelCategoryQuillen.J.rlp p) :
    SSet.modelCategoryQuillen.J.rlp ((exIterate n).map p) := by
  induction n with
  | zero => exact hp
  | succ n ih => exact ex_map_rlp ((exIterate n).map p) ih

/--
概要：Ex∞ は任意の Kan fibration を保つ。
方針：反復列の arrow の余極限に、horn の右持ち上げ性の保存を適用する。
規約：Moss 原論文 Proposition 3.12。Kan 性と同様に保存も証明し、追加の入力とはしない。
使われ方：Ex∞ による非 Kan 基底から Kan 基底への移行。
-/
@[kerodon 00ZG]
theorem exInfinity_map_rlp {E B : SSet.{u}} (p : E ⟶ B)
    (hp : SSet.modelCategoryQuillen.J.rlp p) :
    SSet.modelCategoryQuillen.J.rlp (exInfinity.map p) := by
  change SSet.modelCategoryQuillen.J.rlp (colim.map (exSequence.flip.map p))
  exact hornRight_sequentialColimit
    (SerrePositivity.DiagramModel.arrowColimitCoconeIsColimit (exSequence.flip.map p))
    (fun n => exIterate_map_rlp n p hp)

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
