module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.BaseChangeSimplicialOriginalHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LocalKanDiagramStrictification
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.BaseChangeSimplicialBoundaryFiberEquivalence
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-!
概要：元の有限単体の境界で、同じ分類図式の Hom 輸送と元の全 Hom の自然性を実現する。
方針：境界包含と既存の底表示同型を、任意の単体写像に対する比較へ渡す。
規約：境界の quasicategory 性や通常圏の nerve 表示を要求しない。
使われ方：セル延長空間の比較の target 側を同じ元の境界へ揃える。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 大きい標準境界を元の有限鎖の nerve の持ち上げへ写す、同じ底の射。 -/
def cocartesianSimplexBoundaryRestriction (n : ℕ) :
    (boundary n : SSet.{u + 1}) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} (Fin (n + 1)))) :=
  (boundary n).ι ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.localKanDiagramBaseIso.{u} n).hom

instance cocartesianSimplexBoundaryRestriction_mono (n : ℕ) :
    Mono (cocartesianSimplexBoundaryRestriction.{u} n) := by
  dsimp only [cocartesianSimplexBoundaryRestriction]
  infer_instance

variable (n : ℕ) {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin (n + 1)) ⥤ C)
  (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C))

/-- 同じ二つの分類図式を標準境界へ制限した、元の比較 path の Hom 輸送。 -/
def cocartesianSimplexBoundaryHomTransport :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeSimplicialHomTransport (cocartesianSimplexBoundaryRestriction n) k p q

/-- 元の境界全体で同じ比較 path による Hom 輸送は同値。 -/
lemma cocartesianSimplexBoundaryHomTransport_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (cocartesianSimplexBoundaryHomTransport n k p q) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeSimplicialHomTransport_isQCatEquivalence
    (cocartesianSimplexBoundaryRestriction n) k p q

/-- 元の全相対 Hom 上で、標準境界への同じ制限と既存の底変換比較は自然。 -/
def cocartesianSimplexBoundaryOriginalHomIso :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeSimplicialOriginalHomIso (cocartesianSimplexBoundaryRestriction n) k p q

variable (r : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (cocartesianSimplexBoundaryRestriction n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p).val.hom))
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (cocartesianSimplexBoundaryRestriction n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q).val.hom))) _⦋0⦌)

/-- 標準境界の指定値を固定した、構成済みの同じ Hom 輸送の実際の fiber の射。 -/
def cocartesianSimplexBoundaryFiberTransport :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeSimplicialBoundaryFiberTransport
    (cocartesianSimplexBoundaryRestriction n) k p q r

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiber_quasicategory_of_innerFibration

/-- 全有限次元の標準境界で、同じ指定値の fiber の輸送は同値。 -/
lemma cocartesianSimplexBoundaryFiberTransport_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (cocartesianSimplexBoundaryFiberTransport n k p q r) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeSimplicialBoundaryFiberTransport_isQCatEquivalence
    (cocartesianSimplexBoundaryRestriction n) k p q r

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
