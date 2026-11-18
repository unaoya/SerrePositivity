module

public import SerrePositivity.InfinityCategories.Sheaves.NativeWeightedSectionsData

/-!
概要：実 Yoneda の同じ全切断関手の指定余単位に沿う値の輸送を固定する。
方針：既存の右 Kan 条件の輸送を選び、終端の極限性と同じ頂点を保持する。
規約：HTT 5.1.5.6、Kerodon Definition 7.3.1.2（Tag 02Y9）の指定輸送の法則。
使われ方：S8 の全形状の比較で、同じ余単位に両立する錐を使う。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Sheaves
variable {A : SSet.{u}} [Quasicategory A] {E : SSet.{u + 1}} [Quasicategory E]

/-- 実 Yoneda の同じ指定余単位の全輸送を選ぶ。 -/
def nativeWeightedSections_valueTransport
    (O : ((SSet.uliftFunctor.{u + 1, u}).obj A).op ⟶ E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (P : (PresheafInfinity A).op _⦋0⦌) :
    RightKanConeTransport (SSet.opFunctor.map (yonedaInfinityMap A)) O
      (nativeWeightedSections O hE) (nativeWeightedSectionsData O hE).2.val P :=
  Classical.choose (nativeWeightedSections_isRightKanExtension O hE P)

/-- 実 Yoneda の同じ指定余単位の輸送の終端は極限錐。 -/
lemma nativeWeightedSections_valueTransport_isLimit
    (O : ((SSet.uliftFunctor.{u + 1, u}).obj A).op ⟶ E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (P : (PresheafInfinity A).op _⦋0⦌) :
    IsLimitCone (nativeWeightedSections_valueTransport O hE P).cone :=
  Classical.choose_spec (nativeWeightedSections_isRightKanExtension O hE P)

/-- 実 Yoneda の同じ輸送は、元の全切断関手の頂点を保つ。 -/
lemma nativeWeightedSections_valueTransport_vertex
    (O : ((SSet.uliftFunctor.{u + 1, u}).obj A).op ⟶ E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (P : (PresheafInfinity A).op _⦋0⦌) :
    (nativeWeightedSections_valueTransport O hE P).cone.vertex =
      (nativeWeightedSections O hE).app _ P :=
  (nativeWeightedSections_valueTransport O hE P).cone_vertex

end SerrePositivity.InfinityCategories.Sheaves
