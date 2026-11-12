module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatPullbackConeTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LimitDiagramIso

/-!
概要：元の任意の二関手の cospan の Cat_∞ 内での極限錐。
方針：path 置換後の極限錐を図式同型に沿って頂点を保って輸送する。
規約：指定円柱と頂点固定を保持する。二射影と指定 path との照合は別工程。
使われ方：Cat_∞ の引き戻しの存在と全試験写像空間の比較への接続。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]

/-- 概要：元の cospan は既存の引き戻し候補を頂点とする極限錐を持つ。
方針：切断の指定円柱を保ち、置換後の極限錐を輸送する。
規約：極限錐の頂点を同値だけでなく厳密に保持する。
使われ方：元の関手の Cat_∞ 内での引き戻しの存在。 -/
lemma exists_catPullbackCone (p : A ⟶ C) (q : B ⟶ C) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackDiagram p q)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ∧ c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackObject p q) := by
  let t := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeTransport p q
  exact ⟨t.cone, t.isLimit, t.vertex_eq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.catPullbackReplacementCone_vertex p q)⟩

/-- 概要：元の二関手の cospan の Cat_∞ 内の極限錐を選ぶ。
方針：指定円柱と頂点固定を保持する相対輸送から選択する。
規約：二脚の具体的な比較は別に検証し、定義に普遍性を仮定しない。
使われ方：Cat_∞ の元の図式上の実際の引き戻し錐。 -/
def catPullbackCone (p : A ⟶ C) (q : B ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackDiagram p q)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeTransport p q).cone

/-- 概要：元の cospan の選んだ錐は実際に極限錐。
方針：指定円柱を保つ相対輸送の極限性を読む。
規約：元の p、q に fibration 性は要求しない。
使われ方：Cat_∞ の引き戻しの普遍性の入力。 -/
lemma catPullbackCone_isLimit (p : A ⟶ C) (q : B ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (catPullbackCone p q) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeTransport p q).isLimit

/-- 概要：元の cospan の極限錐の頂点は既存の引き戻し候補。
方針：相対輸送の頂点の等式を取り出す。
規約：厳密な頂点の等式を返す。
使われ方：全試験関手 core による引き戻し比較との接続。 -/
lemma catPullbackCone_vertex (p : A ⟶ C) (q : B ⟶ C) :
    (catPullbackCone p q).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackObject p q) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeTransport p q).vertex_eq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.catPullbackReplacementCone_vertex p q)

/-- 概要：任意の二関手の元の cospan は Cat_∞ 内で極限を持つ。
方針：構成した錐とその極限性を組にする。
規約：通常の QCat の strict pullback の存在とは区別する。
使われ方：Cat_∞ の引き戻しの存在の公開界面。 -/
lemma catPullbackDiagram_hasLimit (p : A ⟶ C) (q : B ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackDiagram p q)) :=
  ⟨catPullbackCone p q, catPullbackCone_isLimit p q⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
