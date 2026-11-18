module

public meta import SerrePositivity.Util.Citation

public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsExistence

/-!
概要：元の反対 Yoneda に沿う重み付き切断の全関手と指定変換を同じ選択で固定する。
方針：検証した右 Kan 延長の存在から一つの全関手と変換を選択する。
  文献対応：HTT 5.1.5.6、Kerodon Definition 7.3.1.2（Tag 02Y9）、S8。
規約：頂点ごとの別々の選択に置き換えない。型の正本は drafts/Sheaves/SpaceValued。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]

/-- 元の反対 Yoneda に沿う全切断関手と指定した右 Kan 変換を固定する。
HTT 5.1.5.6、Kerodon Definition 7.3.1.2（Tag 02Y9）。 -/
@[cite HTT "5.1.5.6" (partial := special)
  "小さい通常の site と presentable 係数に対する反対 Yoneda の右 Kan 延長（双対）。全余極限保存関手の圏同値全体はこの宣言に含めない。"]
def weightedSectionsData (O : Presheaf C E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    Σ G : (PresheafCat C SpaceInfinity.{u}).op ⟶ E,
      {ε : SSet.Homotopy (oppositeSpaceYoneda C ≫ G) O //
        IsRightKanExtension (oppositeSpaceYoneda C) O G ε} := by
  let h := exists_weightedSections O hE
  let G := Classical.choose h
  let ε := Classical.choose (Classical.choose_spec h)
  exact ⟨G, ε, Classical.choose_spec (Classical.choose_spec h)⟩

/-- 同じ全重みの切断関手。HTT 5.1.5.6。 -/
abbrev weightedSections (O : Presheaf C E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :=
  (weightedSectionsData O hE).1

/-- 同じ全関手と選んだ変換は右 Kan 延長の条件を満たす。HTT 5.1.5.6。 -/
@[cite HTT "5.1.5.6" (partial := special)
  "小さい通常の site と presentable 係数に対する反対 Yoneda の右 Kan 延長（双対）。全余極限保存関手の圏同値全体はこの宣言に含めない。"]
lemma weightedSections_isRightKanExtension (O : Presheaf C E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    IsRightKanExtension (oppositeSpaceYoneda C) O
      (weightedSections O hE) (weightedSectionsData O hE).2.val :=
  (weightedSectionsData O hE).2.property

/-- 同じ全関手の値を、指定した局所図式の極限錐と同じ頂点で表す。
HTT 5.1.5.6、Kerodon Definition 7.3.1.2（Tag 02Y9）。 -/
lemma weightedSections_limitValue (O : Presheaf C E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (P : (PresheafCat C SpaceInfinity.{u}).op _⦋0⦌) :
    ∃ c : JoinCone (rightKanDiagram (oppositeSpaceYoneda C) O P),
      IsLimitCone c ∧ c.vertex = (weightedSections O hE).app _ P :=
  (weightedSections_isRightKanExtension O hE).limitValue P

end SerrePositivity.InfinityCategories.Sheaves
