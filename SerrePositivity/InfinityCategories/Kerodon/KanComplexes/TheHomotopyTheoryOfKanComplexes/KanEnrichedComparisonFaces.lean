module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedComparisonTriangle

/-!
概要：比較の合成三点図式の面を既存の比較の図式と同定する。
方針：対角評価の添字の二値を分け、同じ対象と豊穣作用を回収する。
規約：既存の比較の辺を選び直さない。
使われ方：全対象の transport の合成三角形の三辺の同定。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 概要：比較の三点図式の最初の二点を選ぶ添字関手。
方針：有限順序の最終点を避ける包含を持ち上げる。
規約：零と一をそのまま保つ。
使われ方：合成三角形の初辺への制限。 -/
def kanEnrichedComparisonFirstIndex : ULift.{u} (Fin 2) ⥤ ULift.{u} (Fin 3) :=
  (show Fin 2 →o Fin 3 from ⟨Fin.castSucc, fun _ _ h ↦ h⟩).uliftMap.toFunctor

/-- 概要：初辺の各対象は元の二点比較の対象。
方針：二つの添字をそれぞれ計算する。
規約：対象の厳密な等式。
使われ方：高次 Hom の比較の始域と終域を揃える。 -/
lemma kanEnrichedComparisonTriangle_first_object {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {F G H : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison F G) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison G H) (X : C)
    (s : ULift.{u} (Fin 2)) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedComparisonTriangle η θ).obj
      (kanEnrichedComparisonFirstIndex.obj s)).obj X =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonDiagram η X).obj s := by
  rcases s with ⟨s⟩
  fin_cases s <;> rfl

/-- 概要：初辺の高次 Hom の混合作用は元の比較の混合作用。
方針：二つの端点とその射を同時に固定して計算する。
規約：対象同定に伴う輸送を明示する。
使われ方：対角評価の全高次の一致を示す局所計算。 -/
lemma kanEnrichedComparisonTriangle_first_mixedHom {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {F G H : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison F G) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison G H) (X Y : C)
    {s t : ULift.{u} (Fin 2)} (f : s ⟶ t) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedComparisonTriangle η θ).mappingSpaceMap X Y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMixedHom (kanEnrichedComparisonFirstIndex.map f)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedComparisonTriangle η θ).evaluate X ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedComparisonTriangle η θ).evaluate Y ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)) ≫
      eqToHom (congrArg₂ (fun U V : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} ↦ SimplicialCategory.sHom U V)
        (kanEnrichedComparisonTriangle_first_object η θ X s)
        (kanEnrichedComparisonTriangle_first_object η θ Y t)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonMappingSpaceMap η X Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMixedHom f
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonDiagram η X ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonDiagram η Y ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) := by
  rcases s with ⟨s⟩
  rcases t with ⟨t⟩
  fin_cases s <;> fin_cases t
  all_goals simp only [eqToHom_refl, Category.comp_id]
  all_goals first
    | (have h := leOfHom f; change (1 : ℕ) ≤ 0 at h; omega)
    | rfl

/-- 概要：合成三点図式の初辺での共同評価は元の比較の共同評価。
方針：添字の二つの値で対象と Hom の計算を揃える。
規約：coherent な対象の図式 T は任意。
使われ方：初辺を既存の比較の辺として回収する。 -/
lemma kanEnrichedComparisonTriangle_first_diagonal {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {F G H : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison F G) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison G H)
    {I : Type u} [LinearOrder I] (σ : I ⥤ ULift.{u} (Fin 2))
    (T : EnrichedFunctor SSet.{u} (SimplicialThickening I) C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramEvaluation (σ ⋙ kanEnrichedComparisonFirstIndex)
        (T.comp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedComparisonTriangle η θ).toEnrichedFunctor) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramEvaluation σ (T.comp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonArrowEnriched η)) := by
  refine EnrichedFunctor.ext SSet
    (fun i ↦ kanEnrichedComparisonTriangle_first_object η θ (T.obj i) (σ.obj i.as)) ?_
  intro i j
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro P
  have hij : i.as ≤ j.as := SimplicialThickening.Path.le (P.obj 0)
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom (σ ⋙ kanEnrichedComparisonFirstIndex)
    (T.comp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedComparisonTriangle η θ).toEnrichedFunctor) i j) ≫
      eqToHom _).app n P =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom σ (T.comp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonArrowEnriched η)) i j).app n P
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom_of_le _ _ i j hij, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom_of_le _ _ i j hij]
  change ((T.map i j ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedComparisonTriangle η θ).mappingSpaceMap _ _) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMixedHom (kanEnrichedComparisonFirstIndex.map (σ.map (homOfLE hij)))
      _ _ ≫ eqToHom _).app n P = _
  rw [Category.assoc, ← Category.assoc _ _ (eqToHom _),
    kanEnrichedComparisonTriangle_first_mixedHom]
  rfl

/-- 概要：合成三角形の後辺への添字関手。
方針：零頂点を除く面の順序写像を持ち上げる。
規約：零と一を一と二へ送る。
使われ方：合成三角形の後辺の回収。 -/
def kanEnrichedComparisonSecondIndex : ULift.{u} (Fin 2) ⥤ ULift.{u} (Fin 3) :=
  (SimplexCategory.δ (0 : Fin 3)).toOrderHom.uliftMap.toFunctor

/-- 概要：後辺の各対象は元の二点比較の対象。
方針：二つの添字をそれぞれ計算する。
規約：対象の厳密な等式。
使われ方：高次 Hom の比較の始域と終域を揃える。 -/
lemma kanEnrichedComparisonTriangle_second_object {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {F G H : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison F G) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison G H) (X : C)
    (s : ULift.{u} (Fin 2)) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedComparisonTriangle η θ).obj
      (kanEnrichedComparisonSecondIndex.obj s)).obj X =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonDiagram θ X).obj s := by
  rcases s with ⟨s⟩
  fin_cases s <;> rfl

/-- 概要：後辺の高次 Hom の混合作用は元の比較の混合作用。
方針：二つの端点とその射を同時に固定して計算する。
規約：対象同定に伴う輸送を明示する。
使われ方：対角評価の全高次の一致を示す局所計算。 -/
lemma kanEnrichedComparisonTriangle_second_mixedHom {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {F G H : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison F G) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison G H) (X Y : C)
    {s t : ULift.{u} (Fin 2)} (f : s ⟶ t) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedComparisonTriangle η θ).mappingSpaceMap X Y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMixedHom (kanEnrichedComparisonSecondIndex.map f)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedComparisonTriangle η θ).evaluate X ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedComparisonTriangle η θ).evaluate Y ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)) ≫
      eqToHom (congrArg₂ (fun U V : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} ↦ SimplicialCategory.sHom U V)
        (kanEnrichedComparisonTriangle_second_object η θ X s)
        (kanEnrichedComparisonTriangle_second_object η θ Y t)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonMappingSpaceMap θ X Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMixedHom f
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonDiagram θ X ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonDiagram θ Y ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) := by
  rcases s with ⟨s⟩
  rcases t with ⟨t⟩
  fin_cases s <;> fin_cases t
  all_goals simp only [eqToHom_refl, Category.comp_id]
  all_goals first
    | (have h := leOfHom f; change (1 : ℕ) ≤ 0 at h; omega)
    | rfl

/-- 概要：合成三点図式の後辺での共同評価は元の比較の共同評価。
方針：添字の二つの値で対象と Hom の計算を揃える。
規約：coherent な対象の図式 T は任意。
使われ方：後辺を既存の比較の辺として回収する。 -/
lemma kanEnrichedComparisonTriangle_second_diagonal {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {F G H : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison F G) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison G H)
    {I : Type u} [LinearOrder I] (σ : I ⥤ ULift.{u} (Fin 2))
    (T : EnrichedFunctor SSet.{u} (SimplicialThickening I) C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramEvaluation (σ ⋙ kanEnrichedComparisonSecondIndex)
        (T.comp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedComparisonTriangle η θ).toEnrichedFunctor) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramEvaluation σ (T.comp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonArrowEnriched θ)) := by
  refine EnrichedFunctor.ext SSet
    (fun i ↦ kanEnrichedComparisonTriangle_second_object η θ (T.obj i) (σ.obj i.as)) ?_
  intro i j
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro P
  have hij : i.as ≤ j.as := SimplicialThickening.Path.le (P.obj 0)
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom (σ ⋙ kanEnrichedComparisonSecondIndex)
    (T.comp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedComparisonTriangle η θ).toEnrichedFunctor) i j) ≫
      eqToHom _).app n P =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom σ (T.comp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonArrowEnriched θ)) i j).app n P
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom_of_le _ _ i j hij, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom_of_le _ _ i j hij]
  change ((T.map i j ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedComparisonTriangle η θ).mappingSpaceMap _ _) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMixedHom (kanEnrichedComparisonSecondIndex.map (σ.map (homOfLE hij)))
      _ _ ≫ eqToHom _).app n P = _
  rw [Category.assoc, ← Category.assoc _ _ (eqToHom _),
    kanEnrichedComparisonTriangle_second_mixedHom]
  rfl

/-- 概要：合成三角形の長辺への添字関手。
方針：中間頂点を除く面の順序写像を持ち上げる。
規約：零と一を零と二へ送る。
使われ方：合成三角形の長辺の回収。 -/
def kanEnrichedComparisonLongIndex : ULift.{u} (Fin 2) ⥤ ULift.{u} (Fin 3) :=
  (SimplexCategory.δ (1 : Fin 3)).toOrderHom.uliftMap.toFunctor

/-- 概要：長辺の各対象は元の二点比較の対象。
方針：二つの添字をそれぞれ計算する。
規約：対象の厳密な等式。
使われ方：高次 Hom の比較の始域と終域を揃える。 -/
lemma kanEnrichedComparisonTriangle_long_object {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {F G H : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison F G) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison G H) (X : C)
    (s : ULift.{u} (Fin 2)) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedComparisonTriangle η θ).obj
      (kanEnrichedComparisonLongIndex.obj s)).obj X =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonDiagram (η.trans θ) X).obj s := by
  rcases s with ⟨s⟩
  fin_cases s <;> rfl

/-- 概要：長辺の高次 Hom の混合作用は元の比較の混合作用。
方針：二つの端点とその射を同時に固定して計算する。
規約：対象同定に伴う輸送を明示する。
使われ方：対角評価の全高次の一致を示す局所計算。 -/
lemma kanEnrichedComparisonTriangle_long_mixedHom {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {F G H : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison F G) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison G H) (X Y : C)
    {s t : ULift.{u} (Fin 2)} (f : s ⟶ t) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedComparisonTriangle η θ).mappingSpaceMap X Y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMixedHom (kanEnrichedComparisonLongIndex.map f)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedComparisonTriangle η θ).evaluate X ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedComparisonTriangle η θ).evaluate Y ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)) ≫
      eqToHom (congrArg₂ (fun U V : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} ↦ SimplicialCategory.sHom U V)
        (kanEnrichedComparisonTriangle_long_object η θ X s)
        (kanEnrichedComparisonTriangle_long_object η θ Y t)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonMappingSpaceMap (η.trans θ) X Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMixedHom f
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonDiagram (η.trans θ) X ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonDiagram (η.trans θ) Y ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) := by
  rcases s with ⟨s⟩
  rcases t with ⟨t⟩
  fin_cases s <;> fin_cases t
  all_goals simp only [eqToHom_refl, Category.comp_id]
  all_goals first
    | (have h := leOfHom f; change (1 : ℕ) ≤ 0 at h; omega)
    | rfl

/-- 概要：合成三点図式の長辺での共同評価は元の比較の共同評価。
方針：添字の二つの値で対象と Hom の計算を揃える。
規約：coherent な対象の図式 T は任意。
使われ方：長辺を既存の比較の辺として回収する。 -/
lemma kanEnrichedComparisonTriangle_long_diagonal {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {F G H : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison F G) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison G H)
    {I : Type u} [LinearOrder I] (σ : I ⥤ ULift.{u} (Fin 2))
    (T : EnrichedFunctor SSet.{u} (SimplicialThickening I) C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramEvaluation (σ ⋙ kanEnrichedComparisonLongIndex)
        (T.comp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedComparisonTriangle η θ).toEnrichedFunctor) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramEvaluation σ
        (T.comp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonArrowEnriched (η.trans θ))) := by
  refine EnrichedFunctor.ext SSet
    (fun i ↦ kanEnrichedComparisonTriangle_long_object η θ (T.obj i) (σ.obj i.as)) ?_
  intro i j
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro P
  have hij : i.as ≤ j.as := SimplicialThickening.Path.le (P.obj 0)
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom (σ ⋙ kanEnrichedComparisonLongIndex)
    (T.comp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedComparisonTriangle η θ).toEnrichedFunctor) i j) ≫
      eqToHom _).app n P =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom σ
      (T.comp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonArrowEnriched (η.trans θ))) i j).app n P
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom_of_le _ _ i j hij, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom_of_le _ _ i j hij]
  change ((T.map i j ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedComparisonTriangle η θ).mappingSpaceMap _ _) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMixedHom (kanEnrichedComparisonLongIndex.map (σ.map (homOfLE hij)))
      _ _ ≫ eqToHom _).app n P = _
  rw [Category.assoc, ← Category.assoc _ _ (eqToHom _),
    kanEnrichedComparisonTriangle_long_mixedHom]
  rfl

/-- 概要：合成三点図式の first の面は既存の比較の族と厳密に一致する。
方針：uncurry 後の共同評価を対角評価の比較で同定する。
規約：全対象と全高次の射を同時に保つ。
使われ方：三辺を元の比較の辺として回収する。 -/
lemma kanEnrichedComparisonTriangleFamily_first {C : Type (u + 1)} [Category.{u} C]
    [SimplicialCategory C] {F G H : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison F G) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison G H) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedComparisonTriangleFamily η θ ≫
      (pre ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap
        kanEnrichedComparisonFirstIndex))).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonFamily η := by
  apply uncurry_injective
  rw [uncurry_pre_app]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedComparisonTriangleFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram.realization,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonFamily, uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramRealization, uncurry_curry]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, T⟩
  exact kanEnrichedComparisonTriangle_first_diagonal η θ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramSimplexBase σ.down) T

/-- 概要：合成三点図式の second の面は既存の比較の族と厳密に一致する。
方針：uncurry 後の共同評価を対角評価の比較で同定する。
規約：全対象と全高次の射を同時に保つ。
使われ方：三辺を元の比較の辺として回収する。 -/
lemma kanEnrichedComparisonTriangleFamily_second {C : Type (u + 1)} [Category.{u} C]
    [SimplicialCategory C] {F G H : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison F G) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison G H) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedComparisonTriangleFamily η θ ≫
      (pre ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap
        kanEnrichedComparisonSecondIndex))).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonFamily θ := by
  apply uncurry_injective
  rw [uncurry_pre_app]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedComparisonTriangleFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram.realization,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonFamily, uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramRealization, uncurry_curry]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, T⟩
  exact kanEnrichedComparisonTriangle_second_diagonal η θ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramSimplexBase σ.down) T

/-- 概要：合成三点図式の long の面は既存の比較の族と厳密に一致する。
方針：uncurry 後の共同評価を対角評価の比較で同定する。
規約：全対象と全高次の射を同時に保つ。
使われ方：三辺を元の比較の辺として回収する。 -/
lemma kanEnrichedComparisonTriangleFamily_long {C : Type (u + 1)} [Category.{u} C]
    [SimplicialCategory C] {F G H : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison F G) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison G H) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedComparisonTriangleFamily η θ ≫
      (pre ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap
        kanEnrichedComparisonLongIndex))).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonFamily (η.trans θ) := by
  apply uncurry_injective
  rw [uncurry_pre_app]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedComparisonTriangleFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram.realization,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonFamily, uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramRealization, uncurry_curry]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, T⟩
  exact kanEnrichedComparisonTriangle_long_diagonal η θ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramSimplexBase σ.down) T

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
