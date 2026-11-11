module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.RelativeFunctorOverEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftFibrationFiberReflection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.EquivalenceTerminal

/-!
概要：前合成同値による相対関手空間の比較は厳密な境界条件を固定しても同値。
方針：単射な境界への制限を left fibration とし、その全空間の同値を fiber へ反映する。
規約：比較射自体の単射性は要求しない。
使われ方：輸送円柱から元の全空間への比較を境界固定の空間へ移す。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：相対前合成による比較を厳密な境界図式の fiber へ制限しても同値。
方針：二つの境界制限の left fibration 性と底上の同値の fiber 反映を使う。
規約：j と j≫i が単射であり、比較射 i は前合成同値。
使われ方：Kerodon Lemma 5.6.9.1（Tag 02SN）、端点写像を厳密に固定した輸送円柱比較。 -/
lemma relativeFunctorBoundaryMap_isQCatEquivalence
    {A D C E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (a : A ⟶ B) (i : D ⟶ A) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence i)
    (j : C ⟶ D) [Mono j] [Mono (j ≫ i)]
    (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p ((j ≫ i) ≫ a)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p a (j ≫ i)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p (i ≫ a) j)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p a i) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre_comp p a i j) b) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsQCatEquivalence.isPrecompositionEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeFunctorPre_isQCatEquivalence_of_precompositionEquivalence p a i hi)

/-- 概要：厳密な境界図式を固定した相対関手空間の可縮性は前合成同値で保ち反映される。
方針：境界固定の比較同値の可縮性の不変性を使う。
規約：両境界包含は単射、比較射自体は単射でなくてもよい。
使われ方：円柱の可縮な境界 fiber を元の全空間へ移す。 -/
lemma relativeFunctorBoundary_isContractibleKan_iff
    {A D C E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (a : A ⟶ B) (i : D ⟶ A) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence i)
    (j : C ⟶ D) [Mono j] [Mono (j ≫ i)]
    (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p ((j ≫ i) ≫ a)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p a (j ≫ i)) b) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p (i ≫ a) j) b) :=
  (relativeFunctorBoundaryMap_isQCatEquivalence p a i hi j b).choose.isContractibleKan_iff

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
