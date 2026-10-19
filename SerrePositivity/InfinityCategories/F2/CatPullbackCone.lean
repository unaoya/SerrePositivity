module

public import SerrePositivity.InfinityCategories.F2.CatPullbackDiagramComparison
public import SerrePositivity.InfinityCategories.F2.LimitDiagramIso

/-!
概要：元の任意の二関手の cospan の Cat_∞ 内での極限錐。
方針：path 置換後の極限錐を図式同型に沿って頂点を保って輸送する。
規約：二射影と指定 path との照合は別工程。頂点は既存の引き戻し候補。
使われ方：Cat_∞ の引き戻しの存在と全試験写像空間の比較への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]

/-- 概要：元の cospan は既存の引き戻し候補を頂点とする極限錐を持つ。
方針：置換後の指定極限錐を、切断が与える図式同型で輸送する。
規約：極限錐の頂点を同値だけでなく厳密に保持する。
使われ方：元の関手の Cat_∞ 内での引き戻しの存在。 -/
lemma exists_catPullbackCone (p : A ⟶ C) (q : B ⟶ C) :
    ∃ c : JoinCone (HomotopyLimits.strictCoherentDiagram (catPullbackDiagram p q)),
      IsLimitCone c ∧ c.vertex = coherentVertex (catPullbackObject p q) := by
  obtain ⟨c, hc, hv⟩ := exists_limitCone_of_functorIso
    (catPullbackReplacementDiagramIso p q) (catPullbackReplacementCone p q)
    (catPullbackReplacementCone_isLimit p q)
  exact ⟨c, hc, hv.trans (catPullbackReplacementCone_vertex p q)⟩

/-- 概要：元の二関手の cospan の Cat_∞ 内の極限錐を選ぶ。
方針：頂点を厳密に固定した存在定理から選択する。
規約：二脚の具体的な比較は別に検証し、定義に普遍性を仮定しない。
使われ方：Cat_∞ の元の図式上の実際の引き戻し錐。 -/
def catPullbackCone (p : A ⟶ C) (q : B ⟶ C) :
    JoinCone (HomotopyLimits.strictCoherentDiagram (catPullbackDiagram p q)) :=
  Classical.choose (exists_catPullbackCone p q)

/-- 概要：元の cospan の選んだ錐は実際に極限錐。
方針：頂点を固定した存在定理の選択条件を読む。
規約：元の p、q に fibration 性は要求しない。
使われ方：Cat_∞ の引き戻しの普遍性の入力。 -/
lemma catPullbackCone_isLimit (p : A ⟶ C) (q : B ⟶ C) :
    IsLimitCone (catPullbackCone p q) :=
  (Classical.choose_spec (exists_catPullbackCone p q)).1

/-- 概要：元の cospan の極限錐の頂点は既存の引き戻し候補。
方針：存在定理の頂点の等式を選択条件から取り出す。
規約：厳密な頂点の等式を返す。
使われ方：全試験関手 core による引き戻し比較との接続。 -/
lemma catPullbackCone_vertex (p : A ⟶ C) (q : B ⟶ C) :
    (catPullbackCone p q).vertex = coherentVertex (catPullbackObject p q) :=
  (Classical.choose_spec (exists_catPullbackCone p q)).2

/-- 概要：任意の二関手の元の cospan は Cat_∞ 内で極限を持つ。
方針：構成した錐とその極限性を組にする。
規約：通常の QCat の strict pullback の存在とは区別する。
使われ方：Cat_∞ の引き戻しの存在の公開界面。 -/
lemma catPullbackDiagram_hasLimit (p : A ⟶ C) (q : B ⟶ C) :
    HasLimit (HomotopyLimits.strictCoherentDiagram (catPullbackDiagram p q)) :=
  ⟨catPullbackCone p q, catPullbackCone_isLimit p q⟩

end SerrePositivity.InfinityCategories.F2
