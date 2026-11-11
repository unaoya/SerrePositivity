module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldNativeLiftBoundary
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CellAttachmentExtensionKan

/-!
概要：既存部分の元の Hom を固定したセル延長空間を、同じ scaffold の境界固定 Hom へ写す。
方針：実際のセルの fiber 同型と、同じ native 境界固定比較を合成する。
規約：貼付け写像には単射性を要求せず、元のセルへの制限を保持する。
使われ方：セル降下で元の native 延長空間から分類先への比較を構成するための source 比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration
variable {C : Type u} [Category.{u} C] {a b c d : Over (nerve C)}
  (f : a ⟶ b) (g : a ⟶ c) (i : b ⟶ d) (j : c ⟶ d)
  (hp : IsPushout f.left g.left i.left j.left) [Mono f.left]
  {E F : SSet.{u}} (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
  (q : F ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration q]
  (r : ((SSet.uliftFunctor.{u + 1, u}).obj
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeCoreFunctor p q).obj (Opposite.op c))) _⦋0⦌)

local instance : Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftPre p q f) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.core_cocartesianPullbackNativePre_fibration p q f
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.fibration_uliftFunctor_map _

local instance : Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldPullbackNativeLift.cocartesianScaffoldPullbackMarkedLiftRestriction p q f) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldPullbackNativeLift.cocartesianScaffoldPullbackMarkedLiftRestriction_fibration p q f

/-- 既存部分の指定 Hom の native 延長空間から、同じセルの scaffold 境界固定 Hom への比較。 -/
def cocartesianCellAttachment_scaffoldExtensionPre :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianCellAttachment_sourceExtensionFiberIso f g i j hp p q r).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldNativeLiftBoundaryPre p q f
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftPre p q g).app (Opposite.op ⦋0⦌) r)

/-- 同じセル延長比較は、元のセル制限と同じ native core 比較を保持する。 -/
lemma cocartesianCellAttachment_scaffoldExtensionPre_ι :
    cocartesianCellAttachment_scaffoldExtensionPre f g i j hp p q r ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldPullbackNativeLift.cocartesianScaffoldPullbackMarkedLiftRestriction p q f)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldPullbackNativeLift.cocartesianScaffoldPullbackNativeLiftPre p q a).app (Opposite.op ⦋0⦌)
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftPre p q g).app (Opposite.op ⦋0⦌) r)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftPre p q j) r ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftPre p q i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldPullbackNativeLift.cocartesianScaffoldPullbackNativeLiftPre p q b := by
  unfold cocartesianCellAttachment_scaffoldExtensionPre
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldNativeLiftBoundaryPre_ι, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianCellAttachment_sourceExtensionFiberIso_hom_ι, Category.assoc]

/-- 任意のセル付加で、元の指定 Hom の延長空間からの同じ scaffold 比較は同値。 -/
lemma cocartesianCellAttachment_scaffoldExtensionPre_isPrecompositionEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence
      (cocartesianCellAttachment_scaffoldExtensionPre f g i j hp p q r) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianCellAttachment_nativeRestriction_fibration f g i j hp p q
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianCellAttachment_sourceExtensionFiberIso f g i j hp p q r)).isQCatEquivalence.comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldNativeLiftBoundaryPre_isQCatEquivalence p q f
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftPre p q g).app (Opposite.op ⦋0⦌) r))
  exact h.isPrecompositionEquivalence

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
