module

public import SerrePositivity.InfinityCategories.Sheaves.NativeWeightedSections

/-!
概要：一般重みの全切断関手と指定右 Kan 変換を同じ選択で固定する。
方針：構成した存在定理の一つの選択から、全関手・変換・局所極限を回収する。
使われ方：HTT 5.1.5.6、Kerodon §8.4（Tag 03V7）の重み付き切断。
規約：頂点ごとに別の関手を選ばない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
namespace SerrePositivity.InfinityCategories.Sheaves
variable {A : SSet.{u}} [Quasicategory A] {E : SSet.{u + 1}} [Quasicategory E]

/-- 同じ全切断関手と指定した右 Kan 変換を固定する。 -/
def nativeWeightedSectionsData
    (O : ((SSet.uliftFunctor.{u + 1, u}).obj A).op ⟶ E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    Σ G : (PresheafInfinity A).op ⟶ E,
      {ε : SSet.Homotopy (SSet.opFunctor.map (yonedaInfinityMap A) ≫ G) O //
        IsRightKanExtension (SSet.opFunctor.map (yonedaInfinityMap A)) O G ε} := by
  let h := exists_nativeWeightedSections hE O
  let G := Classical.choose h
  let ε := Classical.choose (Classical.choose_spec h)
  exact ⟨G, ε, Classical.choose_spec (Classical.choose_spec h)⟩

/-- 全重みの同じ切断関手。 -/
abbrev nativeWeightedSections
    (O : ((SSet.uliftFunctor.{u + 1, u}).obj A).op ⟶ E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :=
  (nativeWeightedSectionsData O hE).1

/-- 選んだ同じ変換は全頂点で右 Kan 延長の条件を満たす。 -/
lemma nativeWeightedSections_isRightKanExtension
    (O : ((SSet.uliftFunctor.{u + 1, u}).obj A).op ⟶ E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    IsRightKanExtension (SSet.opFunctor.map (yonedaInfinityMap A)) O
      (nativeWeightedSections O hE) (nativeWeightedSectionsData O hE).2.val :=
  (nativeWeightedSectionsData O hE).2.property

/-- 同じ全関手の任意の値を、指定局所図式の極限錐と同じ頂点で表す。 -/
lemma nativeWeightedSections_limitValue
    (O : ((SSet.uliftFunctor.{u + 1, u}).obj A).op ⟶ E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (P : (PresheafInfinity A).op _⦋0⦌) :
    ∃ c : JoinCone (rightKanDiagram (SSet.opFunctor.map (yonedaInfinityMap A)) O P),
      IsLimitCone c ∧ c.vertex = (nativeWeightedSections O hE).app _ P :=
  (nativeWeightedSections_isRightKanExtension O hE).limitValue P

end SerrePositivity.InfinityCategories.Sheaves
