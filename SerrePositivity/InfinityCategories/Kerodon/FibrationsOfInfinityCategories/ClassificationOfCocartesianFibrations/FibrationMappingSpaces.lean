module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FibrationInfinity
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Edges

/-!
概要：元の cocartesian fibration の頂点・辺と、可逆な相対変換による実際の写像空間の比較。
方針：指定した射影を束縛し、元の辺を保つ射を coherent nerve の辺へ送る。
規約：写像空間は元の相対関手 ∞ 圏の core との同値であり、全体を Kan と仮定しない。
使われ方：Cat∞ 値分類の充満忠実性を証明するための fibration 側の比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 指定した元の射影を、core Hom を持つ cocartesian fibrations の対象とする。 -/
def cocartesianFibrationObjectOf {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory B :=
  ⟨Over.mk p, inferInstanceAs (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p)⟩

/-- 指定した元の cocartesian fibration を、分類側の ∞ 圏の標準頂点にする。 -/
def cocartesianFibrationInfinityVertex {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationInfinity B) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (cocartesianFibrationObjectOf p)

/-- 元の cocartesian 辺を保つ指定した底上の射は、そのまま分類側の ∞ 圏の辺を定める。 -/
def cocartesianFibrationInfinityEdge {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PreservesCocartesianEdges p q f) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationInfinity B).Edge
      (cocartesianFibrationInfinityVertex p) (cocartesianFibrationInfinityVertex q) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (show cocartesianFibrationObjectOf p ⟶ cocartesianFibrationObjectOf q from
    ⟨Over.homMk (U := Over.mk p) (V := Over.mk q) f hf, hc⟩)

/-- 元の cocartesian な底上の相対関手の core は、同じ ∞ 圏の実際の右写像空間と同値。 -/
def cocartesianFibrationInfinityMappingEquivalence {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration q] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      ((SSet.uliftFunctor.{u + 1, u}).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace p q) : SSet.{u}))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (cocartesianFibrationInfinityVertex p) (cocartesianFibrationInfinityVertex q)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomEquivalence (cocartesianFibrationObjectOf p) (cocartesianFibrationObjectOf q)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
