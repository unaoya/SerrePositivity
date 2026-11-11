module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictDiagramMixedHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramSimplicialCategory

/-!
概要：通常の底の図式と coherent な strict な Kan 値図式の対角評価。
方針：二端点が順序を持つ場合は混合 Hom の作用を使い、逆向きは空の path から射を作る。
規約：順序の各対象で対応する図式の値を Kan 複体として取る。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、二つの添字を同時に動かす分類関手の単体。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：底の図式と coherent な Kan 値図式 の同じ添字を評価する。
方針：図式の対応する対象で Kan 複体の値を取る。
規約：通常の図式 A は順序 J を始域とする。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、対角 coherent 図式の対象の作用。 -/
def diagonalKanDiagramObject {C : Type u} [Category.{u} C] {J : Type u} [LinearOrder J]
    (A : J ⥤ C)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening J) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject C))
    (i : SimplicialThickening J) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  (F.obj i).val.obj (A.obj i.as)

/-- 概要：対角評価の二対象間の豊穣 Hom の作用。
方針：順向きでは strict な変換空間を混合作用で写し、逆向きでは path の不存在を使う。
規約：順序の証明の選択は射を変えない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、対角 coherent 図式の Hom の作用。 -/
noncomputable def diagonalKanDiagramHom {C : Type u} [Category.{u} C] {J : Type u} [LinearOrder J]
    (A : J ⥤ C)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening J) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject C))
    (i j : SimplicialThickening J) :
    SimplicialCategory.sHom i j ⟶
      SimplicialCategory.sHom (diagonalKanDiagramObject A F i) (diagonalKanDiagramObject A F j) :=
  if h : i.as ≤ j.as then
    F.map i j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMixedHom (A.map (homOfLE h))
      ((F.obj i).val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) ((F.obj j).val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
  else
    { app n := ↾fun P ↦ (h (SimplicialThickening.Path.le (P.obj 0))).elim
      naturality {n m} α := by
        apply ConcreteCategory.hom_ext
        intro P
        exact (h (SimplicialThickening.Path.le (P.obj 0))).elim }

/-- 概要：端点が順方向なら対角評価の Hom は混合作用の式に一致する。
方針：順序による分岐の肯定側を計算する。
規約：h の証明は任意。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、対角評価の単位則と合成則の検証。 -/
lemma diagonalKanDiagramHom_of_le {C : Type u} [Category.{u} C] {J : Type u} [LinearOrder J]
    (A : J ⥤ C)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening J) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject C))
    (i j : SimplicialThickening J) (h : i.as ≤ j.as) :
    diagonalKanDiagramHom A F i j =
      F.map i j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMixedHom (A.map (homOfLE h))
      ((F.obj i).val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) ((F.obj j).val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) :=
  dite_eq_left h

/-- 概要：二つの図式の対角評価は thickening から Kan 複体への豊穣関手。
方針：順向きの Hom では混合作用の単位則・合成則を使い、空の Hom の場合を除く。
規約：底 C は通常の圏。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、分類関手の二変数の単体の組立て。 -/
noncomputable def diagonalKanDiagramEvaluation {C : Type u} [Category.{u} C] {J : Type u} [LinearOrder J]
    (A : J ⥤ C)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening J) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject C)) :
    EnrichedFunctor SSet.{u} (SimplicialThickening J) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} where
  obj := diagonalKanDiagramObject A F
  map := diagonalKanDiagramHom A F
  map_id i := by
    rw [diagonalKanDiagramHom_of_le A F i i le_rfl, ← Category.assoc, F.map_id]
    have hA : A.map (homOfLE (le_refl i.as)) = 𝟙 (A.obj i.as) := A.map_id _
    rw [hA]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMixedHom_id ((F.obj i).val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (A.obj i.as)
  map_comp i j k := by
    by_cases hij : i.as ≤ j.as
    · by_cases hjk : j.as ≤ k.as
      · rw [diagonalKanDiagramHom_of_le A F i k (hij.trans hjk),
          diagonalKanDiagramHom_of_le A F i j hij, diagonalKanDiagramHom_of_le A F j k hjk]
        rw [← Category.assoc, F.map_comp, Category.assoc]
        have hA : A.map (homOfLE (hij.trans hjk)) =
            A.map (homOfLE hij) ≫ A.map (homOfLE hjk) := by
          rw [← A.map_comp]
          rfl
        change (F.map i j ⊗ₘ F.map j k) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingComposition ((F.obj i).val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
            ((F.obj j).val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) ((F.obj k).val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMixedHom (A.map (homOfLE (hij.trans hjk)))
            ((F.obj i).val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) ((F.obj k).val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) =
          (F.map i j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMixedHom (A.map (homOfLE hij))
              ((F.obj i).val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) ((F.obj j).val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) ⊗ₘ
            F.map j k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMixedHom (A.map (homOfLE hjk))
              ((F.obj j).val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) ((F.obj k).val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)) ≫
            MonoidalClosed.comp (diagonalKanDiagramObject A F i).obj
              (diagonalKanDiagramObject A F j).obj (diagonalKanDiagramObject A F k).obj
        rw [hA, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMixedHom_comp, tensorHom_comp_tensorHom_assoc]
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
