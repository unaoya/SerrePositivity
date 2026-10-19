module

public import SerrePositivity.InfinityCategories.F2.ContinuousKanAnodyne
public import SerrePositivity.InfinityCategories.F2.ContinuousKanFilling
public import SerrePositivity.InfinityCategories.F1B.WeakHomotopy
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanSourceReplacement

/-!
概要：具体的な連続 Kan 置換への単位は弱ホモトピー同値。
方針：証明済みの anodyne 性から Kan 標的への前合成のホモトピー同値を使う。
規約：既存の N の Kan 標的の比較は読み取り専用で再利用する。
使われ方：有限部分での収縮を連続 Kan 置換後に移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：連続 Kan 置換への元の単位は全ての対象で弱ホモトピー同値。
方針：Kan 標的への前合成のホモトピー同値から連結成分の全単射を取る。
規約：X 自体の Kan 性も quasicategory 性も不要。
使われ方：一般の filtered ∞ 圏の弱可縮性を Kan 複体で判定する。 -/
lemma continuousKanReplacementUnit_isWeakHomotopyEquivalence (X : SSet.{u}) :
    IsWeakHomotopyEquivalence (continuousKanReplacementUnit.app X) := by
  intro Z _
  exact (HomotopyLimits.homotopyEquivalence_pre_of_anodyne _
    (continuousKanReplacementUnit_anodyne X) Z).mapPiZero_bijective

end SerrePositivity.InfinityCategories.F2
