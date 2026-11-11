module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.DiagonalQuasicategoryDiagramHom

/-!
概要：quasicategory 値 図式の対角評価の豊穣単位と合成。
方針：順向きの Hom は元の core の混合作用を使い、逆向きは空の path から写す。
規約：全高次の変換を保持した QCat 値の評価を構成する。
使われ方：Cat∞ 値関手への実現の各単体。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：二つの図式の対角評価は thickening から quasicategoryへの豊穣関手。
方針：順向きの Hom では混合作用の単位則・合成則を使い、空の Hom の場合を除く。
規約：底 C は通常の圏。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、分類関手の二変数の単体の組立て。 -/
noncomputable def diagonalQuasicategoryDiagramEvaluation {C : Type u} [Category.{u} C] {J :
  Type u} [LinearOrder J]
    (A : J ⥤ C)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening J) (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryDiagramCategory
      C)) :
    EnrichedFunctor SSet.{u} (SimplicialThickening J) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u} where
  obj := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalQuasicategoryDiagramObject A F
  map := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalQuasicategoryDiagramHom A F
  map_id i := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalQuasicategoryDiagramHom_of_le A F i i le_rfl, ← Category.assoc, F.map_id]
    have hA : A.map (homOfLE (le_refl i.as)) = 𝟙 (A.obj i.as) := A.map_id _
    rw [hA]
    exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramMixedHom_id (F.obj i) (A.obj i.as)
  map_comp i j k := by
    by_cases hij : i.as ≤ j.as
    · by_cases hjk : j.as ≤ k.as
      · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalQuasicategoryDiagramHom_of_le A F i k (hij.trans hjk),
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalQuasicategoryDiagramHom_of_le A F i j hij,
            _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalQuasicategoryDiagramHom_of_le A F j k hjk]
        rw [← Category.assoc, F.map_comp, Category.assoc]
        have hA : A.map (homOfLE (hij.trans hjk)) =
            A.map (homOfLE hij) ≫ A.map (homOfLE hjk) := by
          rw [← A.map_comp]
          rfl
        change (F.map i j ⊗ₘ F.map j k) ≫
          eComp SSet (F.obj i) (F.obj j) (F.obj k) ≫
          _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramMixedHom (A.map (homOfLE (hij.trans hjk)))
            (F.obj i) (F.obj k) =
          (F.map i j ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramMixedHom (A.map (homOfLE hij))
              (F.obj i) (F.obj j) ⊗ₘ
            F.map j k ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramMixedHom (A.map (homOfLE hjk))
              (F.obj j) (F.obj k)) ≫
            eComp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalQuasicategoryDiagramObject A F i)
              (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalQuasicategoryDiagramObject A F j)
                (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalQuasicategoryDiagramObject A F k)
        rw [hA, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramMixedHom_comp, tensorHom_comp_tensorHom_assoc]
        rfl
      · apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        rintro ⟨P, Q⟩
        exact (hjk (SimplicialThickening.Path.le (Q.obj 0))).elim
    · apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      rintro ⟨P, Q⟩
      exact (hij (SimplicialThickening.Path.le (P.obj 0))).elim

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
