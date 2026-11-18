module

public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsData

/-!
概要：元の全切断関手の同じ指定余単位に沿う値の輸送を固定する。
方針：右 Kan 条件の輸送そのものを選び、その終端の極限性と頂点の等式を取り出す。
規約：HTT 5.1.5.6、Kerodon Definition 7.3.1.2（Tag 02Y9）の指定輸送の法則。
使われ方：S8 の値の比較に、元の余単位との両立を保持する。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]

/-- 元の同じ指定余単位の全時間の輸送を選び、値だけの存在命題には忘却しない。 -/
def weightedSections_valueTransport (O : Presheaf C E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (P : (PresheafCat C SpaceInfinity.{u}).op _⦋0⦌) :
    RightKanConeTransport (oppositeSpaceYoneda C) O (weightedSections O hE)
      (weightedSectionsData O hE).2.val P :=
  Classical.choose (weightedSections_isRightKanExtension O hE P)

/-- 同じ指定余単位の輸送の終端は極限錐。 -/
lemma weightedSections_valueTransport_isLimit (O : Presheaf C E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (P : (PresheafCat C SpaceInfinity.{u}).op _⦋0⦌) :
    IsLimitCone (weightedSections_valueTransport O hE P).cone :=
  Classical.choose_spec (weightedSections_isRightKanExtension O hE P)

/-- 同じ指定余単位の輸送は、元の全切断関手の頂点を保つ。 -/
lemma weightedSections_valueTransport_vertex (O : Presheaf C E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (P : (PresheafCat C SpaceInfinity.{u}).op _⦋0⦌) :
    (weightedSections_valueTransport O hE P).cone.vertex = (weightedSections O hE).app _ P :=
  (weightedSections_valueTransport O hE P).cone_vertex

end SerrePositivity.InfinityCategories.Sheaves
