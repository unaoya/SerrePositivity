module

public import SerrePositivity.InfinityCategories.F2.LaxPullbackLimitCriterion
public import SerrePositivity.InfinityCategories.F2.ExactFunctorSpanCospanPreservation
public import SerrePositivity.InfinityCategories.F2.LaxPullbackZeroProjections
public import SerrePositivity.InfinityCategories.F2.SpecifiedFiberCospan

/-!
概要：零対象からの第二枝を持つ lax pullback の指定 cospan の極限。
方針：両射影の零保存で入力の安定圏の存在を使い、完全性から像の保存を導く。
規約：lax pullback の安定性や全有限極限を仮定しない。
使われ方：fiber の存在と射影の完全性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]
variable [IsStable A] [IsStable B] (p : A ⟶ C) (q : B ⟶ C)
variable [IsExactFunctor p] [IsExactFunctor q]

/-- 概要：第二枝の始点が零対象である cospan の両入力は極限を持つ。
方針：元の二関手の完全性から両射影の零保存を使い、安定圏の零枝の存在を適用する。
規約：入力の二つの cospan は元の射影による図式。
使われ方：lax pullback の零角四角形の成分判定の存在条件。 -/
lemma laxPullback_cospan_input_limits_of_zero_second
    (r : (horn 2 2 : SSet.{u}) ⟶ laxPullback p q)
    (hz : IsZeroVertex ((horn₂₂.ι₁₂ ≫ r).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))) :
    HasLimit (r ≫ laxPullbackFst p q) ∧ HasLimit (r ≫ laxPullbackSnd p q) := by
  constructor
  · apply hasLimit_cospan_of_zero_second
    change IsZeroVertex ((laxPullbackFst p q).app (Opposite.op ⦋0⦌)
      ((horn₂₂.ι₁₂ ≫ r).app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))))
    exact laxPullbackFst_preservesZero p q (IsExactFunctor.preservesZero (F := p))
      (IsExactFunctor.preservesZero (F := q)) _ hz
  · apply hasLimit_cospan_of_zero_second
    change IsZeroVertex ((laxPullbackSnd p q).app (Opposite.op ⦋0⦌)
      ((horn₂₂.ι₁₂ ≫ r).app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))))
    exact laxPullbackSnd_preservesZero p q (IsExactFunctor.preservesZero (F := p))
      (IsExactFunctor.preservesZero (F := q)) _ hz

variable [IsStable C]

/-- 概要：第二枝が零対象から出る指定 cospan は lax pullback で極限を持つ。
方針：入力の安定性による存在と元の完全関手の cospan 極限保存を使う。
規約：元の指定された cospan 全体を固定する。
使われ方：fiber 四角形の構成。 -/
lemma hasLimit_laxPullback_cospan_of_zero_second
    (r : (horn 2 2 : SSet.{u}) ⟶ laxPullback p q)
    (hz : IsZeroVertex ((horn₂₂.ι₁₂ ≫ r).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))) : HasLimit r := by
  obtain ⟨ha, hb⟩ := laxPullback_cospan_input_limits_of_zero_second p q r hz
  exact hasLimit_laxPullback_of_components p q r ha hb
    (fun c hc ↦ exactFunctor_preserves_cospan_limit p c hc)
    (fun c hc ↦ exactFunctor_preserves_cospan_limit q c hc)

end SerrePositivity.InfinityCategories.F2
