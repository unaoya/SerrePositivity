module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedComparisonComposition

/-!
概要：二つの豊穣比較とその合成を一つの三点図式にする。
方針：三頂点を元の関手とし、長辺を実際の成分の合成とする。
規約：比較の三辺を変更しない。
使われ方：全対象の transport の合成三角形の coherent な実現。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 概要：二つの豊穣比較の合成三角形を厳密な図式として束ねる。
方針：三つの関手と比較、恒等、成分の合成を三点の順序に配置する。
規約：長辺は η.trans θ そのもの。
使われ方：合成則を実際の coherent な三角形で実現する。 -/
def kanEnrichedComparisonTriangle {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {F G H : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison F G) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison G H) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C (ULift.{u} (Fin 3)) where
  obj j := Fin.cases (motive := fun _ : Fin 3 ↦ EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) F
    (fun k ↦ Fin.cases (motive := fun _ : Fin 2 ↦
      EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) G (fun _ ↦ H) k) j.down
  map {i j} f := match i, j, f with
    | ⟨0⟩, ⟨0⟩, _ => .identity F
    | ⟨0⟩, ⟨1⟩, _ => η
    | ⟨0⟩, ⟨2⟩, _ => η.trans θ
    | ⟨1⟩, ⟨0⟩, f => (by
      have h := leOfHom f
      change (1 : ℕ) ≤ 0 at h
      exact (by omega : False).elim)
    | ⟨1⟩, ⟨1⟩, _ => .identity G
    | ⟨1⟩, ⟨2⟩, _ => θ
    | ⟨2⟩, ⟨0⟩, f => (by
      have h := leOfHom f
      change (2 : ℕ) ≤ 0 at h
      exact (by omega : False).elim)
    | ⟨2⟩, ⟨1⟩, f => (by
      have h := leOfHom f
      change (2 : ℕ) ≤ 1 at h
      exact (by omega : False).elim)
    | ⟨2⟩, ⟨2⟩, _ => .identity H
  map_id i X := by
    rcases i with ⟨i⟩
    fin_cases i <;> rfl
  map_comp {i j k} f g X := by
    have hij := leOfHom f
    have hjk := leOfHom g
    rcases i with ⟨i⟩
    rcases j with ⟨j⟩
    rcases k with ⟨k⟩
    change i.val ≤ j.val at hij
    change j.val ≤ k.val at hjk
    fin_cases i <;> fin_cases j <;> fin_cases k
    all_goals try norm_num at hij
    all_goals try norm_num at hjk
    all_goals dsimp [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedComparison.identity, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedComparison.trans]
    all_goals exact (Category.id_comp _).symm

/-- 概要：三点図式の最初の比較は元の η そのもの。
方針：有限順序の最初の非恒等射の定義を計算する。
規約：全対象と全高次 Hom に関する比較の等式。
使われ方：合成三角形の初辺の回収。 -/
lemma kanEnrichedComparisonTriangle_first {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {F G H : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison F G) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison G H) :
    (kanEnrichedComparisonTriangle η θ).map (homOfLE
      (show (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) ≤ ULift.up 1 from by decide)) = η := rfl

/-- 概要：三点図式の後半の比較は元の θ そのもの。
方針：有限順序の後半の非恒等射の定義を計算する。
規約：全対象と全高次 Hom に関する比較の等式。
使われ方：合成三角形の後辺の回収。 -/
lemma kanEnrichedComparisonTriangle_second {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {F G H : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison F G) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison G H) :
    (kanEnrichedComparisonTriangle η θ).map (homOfLE
      (show (ULift.up (1 : Fin 3) : ULift.{u} (Fin 3)) ≤ ULift.up 2 from by decide)) = θ := rfl

/-- 概要：三点図式の長辺は実際の合成比較 η.trans θ。
方針：有限順序の長辺の定義を計算する。
規約：同型な別の比較に置き換えない。
使われ方：比較の合成則の長辺の回収。 -/
lemma kanEnrichedComparisonTriangle_long {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {F G H : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison F G) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison G H) :
    (kanEnrichedComparisonTriangle η θ).map (homOfLE
      (show (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) ≤ ULift.up 2 from by decide)) =
        η.trans θ := rfl

/-- 概要：二つの比較とその合成を全対象上の一つの coherent な三点図式に実現する。
方針：構成した三点図式に任意の比較図式の実現を適用する。
規約：始点・中間点・終点を別々に選ばない。
使われ方：全対象の transport の合成三角形。 -/
def kanEnrichedComparisonTriangleFamily {C : Type (u + 1)} [Category.{u} C]
    [SimplicialCategory C] {F G H : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison F G) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison G H) :
    SimplicialNerve C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinityFunctor
      ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} (Fin 3)))) :=
  (kanEnrichedComparisonTriangle η θ).realization

/-- 概要：合成三点図式の始点は元の F の coherent nerve。
方針：一般の図式の実現の評価公式を使う。
規約：単体集合の射の厳密な等式。
使われ方：合成三角形の始点の同定。 -/
lemma kanEnrichedComparisonTriangleFamily_zero {C : Type (u + 1)} [Category.{u} C]
    [SimplicialCategory C] {F G H : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison F G) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison G H) :
    kanEnrichedComparisonTriangleFamily η θ ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up (0 : Fin 3)))) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap F :=
  (kanEnrichedComparisonTriangle η θ).realization_evaluate _

/-- 概要：合成三点図式の中間点は元の G の coherent nerve。
方針：一般の図式の実現の評価公式を使う。
規約：単体集合の射の厳密な等式。
使われ方：二つの比較の共通端点の同定。 -/
lemma kanEnrichedComparisonTriangleFamily_one {C : Type (u + 1)} [Category.{u} C]
    [SimplicialCategory C] {F G H : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison F G) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison G H) :
    kanEnrichedComparisonTriangleFamily η θ ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up (1 : Fin 3)))) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap G :=
  (kanEnrichedComparisonTriangle η θ).realization_evaluate _

/-- 概要：合成三点図式の終点は元の H の coherent nerve。
方針：一般の図式の実現の評価公式を使う。
規約：単体集合の射の厳密な等式。
使われ方：合成三角形の終点の同定。 -/
lemma kanEnrichedComparisonTriangleFamily_two {C : Type (u + 1)} [Category.{u} C]
    [SimplicialCategory C] {F G H : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison F G) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison G H) :
    kanEnrichedComparisonTriangleFamily η θ ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up (2 : Fin 3)))) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap H :=
  (kanEnrichedComparisonTriangle η θ).realization_evaluate _

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
