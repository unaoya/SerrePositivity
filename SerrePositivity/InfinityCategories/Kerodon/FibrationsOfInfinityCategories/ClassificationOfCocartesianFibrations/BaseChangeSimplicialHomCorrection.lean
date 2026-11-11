module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.BaseChangeSimplicialHomTransportRestriction
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.PathCorrectedFunctorSquare
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingPostLifting
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.PathCorrectedSquarePrecompositionCoherence

/-!
概要：任意の単射な境界への指定自然性を保持して、元の Hom 輸送を厳密に可換にする。
方針：同じ分類先の制限に沿って指定 path を持ち上げ、固定境界 fiber へ制限する。
規約：元の Hom 輸送への指定同型を保持し、境界の nerve 表示を要求しない。
使われ方：セル延長空間の target 側の境界固定の比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable {D C : Type u} [Category.{u} D] [Category.{u} C] {A : SSet.{u + 1}}
  (a : A ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (nerve D)) [Mono a] (k : D ⥤ C)
  (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C))
local notation "R₀" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeSimplicialRestrictionZero a k p q
local notation "R₁" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeSimplicialRestrictionOne a k p q
local notation "U" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomTransport k p q
local notation "V" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeSimplicialHomTransport a k p q

/-- 同じ指定 path を保ち、境界への制限と厳密に可換にした元の Hom 輸送。 -/
def cocartesianBaseChangeSimplicialHomCorrection :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.PathCorrectedFunctorSquare R₀ U (R₁ ≫ V)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomTransport_simplicialRestrictionIso a k p q).symm :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.pathCorrectedFunctorSquare R₀
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanEquivalenceLifting_intervalMappingPostOfEq ((pre a).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.equivalenceLifting_pre a) _ _ rfl rfl) U (R₁ ≫ V)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomTransport_simplicialRestrictionIso a k p q).symm

/-- 補正した同じ全 Hom の輸送。 -/
def cocartesianBaseChangeSimplicialCorrectedHomTransport :=
  (cocartesianBaseChangeSimplicialHomCorrection a k p q).map

/-- 指定された元の境界輸送への制限は厳密に一致する。 -/
lemma cocartesianBaseChangeSimplicialCorrectedHomTransport_comm :
    cocartesianBaseChangeSimplicialCorrectedHomTransport a k p q ≫ R₀ = R₁ ≫ V :=
  (cocartesianBaseChangeSimplicialHomCorrection a k p q).comm

/-- 補正した輸送は、同じ指定 path で元の輸送と同型。 -/
def cocartesianBaseChangeSimplicialCorrectedHomTransportIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (cocartesianBaseChangeSimplicialCorrectedHomTransport a k p q) U :=
  (cocartesianBaseChangeSimplicialHomCorrection a k p q).exactComponentIso

/-- 同じ補正輸送は、追加仮定なしに全 Hom の同値。 -/
lemma cocartesianBaseChangeSimplicialCorrectedHomTransport_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (cocartesianBaseChangeSimplicialCorrectedHomTransport a k p q) :=
  (cocartesianBaseChangeSimplicialHomCorrection a k p q).map_isQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomTransport_isQCatEquivalence k p q)

variable (r : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p).val.hom))
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q).val.hom))) _⦋0⦌)

/-- 指定された境界値を固定した、同じ補正輸送の実際の fiber 上の射。 -/
def cocartesianBaseChangeSimplicialBoundaryFiberTransport :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber R₁ r ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber R₀ ((V).app (Opposite.op ⦋0⦌) r) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift R₀ ((V).app (Opposite.op ⦋0⦌) r)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι R₁ r ≫ cocartesianBaseChangeSimplicialCorrectedHomTransport a k p q) (by
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun m ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι R₁ r ≫ m)
          (cocartesianBaseChangeSimplicialCorrectedHomTransport_comm a k p q)).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun m ↦ m ≫ V) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp R₁ r)).trans
              (SSet.const_comp _ _)))))

/-- 同じ境界固定の射は、元の全 Hom への射影を保持する。 -/
lemma cocartesianBaseChangeSimplicialBoundaryFiberTransport_ι :
    cocartesianBaseChangeSimplicialBoundaryFiberTransport a k p q r ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι R₀ ((V).app (Opposite.op ⦋0⦌) r) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι R₁ r ≫ cocartesianBaseChangeSimplicialCorrectedHomTransport a k p q :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
