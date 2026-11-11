module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ResolutionArrow
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramEvaluation

/-!
概要：解像の標準比較を二点の図式への豊穣関手にまとめる。
方針：strict な変換空間への作用を使い、両端点で豊穣単位と合成を評価する。
規約：始点は恒等豊穣関手、終点は解像の豊穣自己関手になる。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、標準比較を coherent な図式の族へ移す。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：解像への標準比較は二点の strict な図式の豊穣的な族を定める。
方針：始点で元の内部 Hom、終点で解像の豊穣 Hom の作用を計算する。
規約：高次のパラメーターを同時に扱う。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、標準比較の大域的な coherent な実現の入力。 -/
noncomputable def coherentResolutionArrowEnriched :
    EnrichedFunctor SSet.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject (ULift.{u} (Fin 2))) where
  obj X := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentResolutionArrowDiagram X, trivial⟩
  map X Y := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentResolutionArrowMappingSpaceMap X Y
  map_id X := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro t
    apply Subtype.ext
    funext i
    rcases i with ⟨i⟩
    fin_cases i
    · apply CategoryTheory.Functor.functorHom_ext
      intro k α
      apply ConcreteCategory.hom_ext
      intro x
      rfl
    · apply CategoryTheory.Functor.functorHom_ext
      intro k α
      apply ConcreteCategory.hom_ext
      intro x
      apply ULift.ext
      apply SSet.hom_ext
      intro l
      apply ConcreteCategory.hom_ext
      intro s
      rfl
  map_comp X Y Z := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨f, g⟩
    apply Subtype.ext
    funext i
    rcases i with ⟨i⟩
    fin_cases i
    · apply CategoryTheory.Functor.functorHom_ext
      intro k α
      apply ConcreteCategory.hom_ext
      intro x
      change g.app k (α ≫ 𝟙 k) (f.app k (α ≫ 𝟙 k) x) =
        g.app k α (f.app k α x)
      rw [Category.comp_id]
    · apply CategoryTheory.Functor.functorHom_ext
      intro k α
      apply ConcreteCategory.hom_ext
      intro x
      apply ULift.ext
      apply SSet.hom_ext
      intro l
      apply ConcreteCategory.hom_ext
      intro s
      rfl

/-- 概要：標準比較の図式の豊穣的な族は始点で恒等関手を回収する。
方針：対象と零側の Hom の成分を計算する。
規約：始点は ULift した零。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な比較の始点条件。 -/
lemma coherentResolutionArrowEnriched_zero :
    coherentResolutionArrowEnriched.comp SSet
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramEvaluationEnriched (ULift.up (0 : Fin 2))) =
        EnrichedFunctor.id SSet.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro X Y
  simp only [eqToHom_refl, Category.comp_id]
  rfl

/-- 概要：標準比較の図式の豊穣的な族は終点で解像を回収する。
方針：対象と一側の Hom の成分を計算する。
規約：終点は ULift した一。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な比較の終点条件。 -/
lemma coherentResolutionArrowEnriched_one :
    coherentResolutionArrowEnriched.comp SSet
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramEvaluationEnriched (ULift.up (1 : Fin 2))) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionKanEnriched.{u} := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro X Y
  simp only [eqToHom_refl, Category.comp_id]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
