module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplexNerveOver
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FiniteSimplexEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PullbackNativeLiftRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalDiagramOverIsomorphism
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.OverIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NativeHomPresentation

/-!
概要：元の任意の標準単体上の native Hom を、同じ分類先の区間 Hom と比較する。
方針：同じ底上の nerve 表示同型で、既存の有限セルの同じ局所比較を移す。
規約：元の標準単体と元の両端図式を保持する。
使われ方：境界の各面と各端点の実際の分類比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
variable {C : Type u} [Category.{u} C] {n : ℕ}
  (σ : (Δ[n] : SSet.{u}) ⟶ nerve C) (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C))
local notation "P" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram q.val.hom

local instance (z : Over (nerve C)) : InnerFibration (pullback.fst z.hom q.val.hom) :=
  ⟨innerFibrations.pullback_fst z.hom q.val.hom (InnerFibration.mem (q := q.val.hom))⟩

local instance (z : Over (nerve C)) : KanComplex ((SSet.uliftFunctor.{u + 1, u}).obj
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeCoreFunctor p.val.hom q.val.hom).obj (Opposite.op z))) :=
  inferInstanceAs (KanComplex ((SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace (pullback.fst z.hom p.val.hom)
      (pullback.fst z.hom q.val.hom)) : SSet.{u})))

/-- 同じ標準単体上の native Hom と、有限鎖表示の同じ Hom の同型。 -/
def cocartesianStandardSimplexSourceIso :
    (SSet.uliftFunctor.{u + 1, u}).obj
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeCoreFunctor p.val.hom q.val.hom).obj (Opposite.op (Over.mk σ))) ≅
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFibrationBaseChangeCoreEnriched (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplexNerveBaseFunctor σ))).obj p)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFibrationBaseChangeCoreEnriched (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplexNerveBaseFunctor σ))).obj q)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHom_nativePresentation (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplexNerveBaseFunctor σ)) p q]
  exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeCoreFunctor p.val.hom q.val.hom) ⋙
    SSet.uliftFunctor.{u + 1, u}).mapIso (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplexNerveOverIso σ).symm.op

/-- 有限鎖上の分類先 Hom と、同じ標準単体上の分類先 Hom の同型。 -/
def cocartesianStandardSimplexTargetIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplexNerveBaseFunctor σ)) ≫ P))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplexNerveBaseFunctor σ)) ≫ Q)) ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map σ ≫ P))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map σ ≫ Q)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverFunctor P Q).mapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftOverIso (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplexNerveOverIso σ)).op

/-- 同じ元の標準単体の native Hom から同じ分類先 Hom への実際の比較。 -/
def cocartesianStandardSimplexHomComparison :=
  (cocartesianStandardSimplexSourceIso σ p q).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianLocalHomComparison (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplexNerveBaseFunctor σ) p q ≫
      (cocartesianStandardSimplexTargetIso σ p q).hom

/-- Source の同型の順方向は、元の底上の逆同型による同じ直接制限。 -/
lemma cocartesianStandardSimplexSourceIso_hom :
    (cocartesianStandardSimplexSourceIso σ p q).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftPre p.val.hom q.val.hom (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplexNerveOverIso σ).inv := rfl

/-- Target の同型の順方向も、元の底上の同型による同じ直接制限。 -/
lemma cocartesianStandardSimplexTargetIso_hom :
    (cocartesianStandardSimplexTargetIso σ p q).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverPre P Q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftOverMorphism (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplexNerveOverIso σ).hom) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverPre P Q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftOverIso (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplexNerveOverIso σ)).hom = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftOverIso_hom]

/-- 元の任意の標準単体上で、この同じ native 分類比較自身は同値。 -/
lemma cocartesianStandardSimplexHomComparison_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (cocartesianStandardSimplexHomComparison σ p q) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (cocartesianStandardSimplexSourceIso σ p q)).isQCatEquivalence.comp
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianLocalHomComparison_finite_isQCatEquivalence n (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplexNerveBaseFunctor σ) p q).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (cocartesianStandardSimplexTargetIso σ p q)).isQCatEquivalence)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
