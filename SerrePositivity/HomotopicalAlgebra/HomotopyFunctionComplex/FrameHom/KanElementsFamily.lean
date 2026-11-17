module
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.KanHomFamilyOpposite
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalEquivalence

/-!
概要：元の全要素圏のKan化を、同じ反対要素圏の終端augmentationへつなぐ。
方針：既存のnerve反転同型と全augmentationの自然性・反転性を合成する。
規約：底と全作用素を保ち、固定始域のroofとの等式は別に照合する。
使われ方：両変数のsource frameの全係数の規約の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.SimplicialModel
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
variable {I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})

/-- 同じ全係数の元の要素圏のnerveの図式。 -/
abbrev simplexElementsNerveDiagram : I ⥤ SSet.{u} := F ⋙ SimplexNerve.functor

/-- 元のnerveの反転同型を同じ全係数へ前合成する。 -/
def simplexElementsOppositeNerveIso :
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.simplexElementsNerveDiagram F) ⋙ SSet.opFunctor ≅ F ⋙ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.functor :=
  Functor.isoWhiskerLeft F _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.oppositeIso.symm

/-- 同じ元のnerve反転同型のKan化。 -/
def simplexElementsOppositeNerveKanIso :
    FunctorIso (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamilyCoherent ((_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.simplexElementsNerveDiagram F) ⋙ SSet.opFunctor))
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamilyCoherent (F ⋙ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.functor)) := by
  let e := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.simplexElementsOppositeNerveIso F
  have : ∀ i, Quasicategory (((_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.simplexElementsNerveDiagram F) ⋙ SSet.opFunctor).obj i) :=
    fun i => by
      change Quasicategory (nerve (F.obj i).Elements).op
      infer_instance
  have : ∀ i, Quasicategory ((F ⋙ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.functor).obj i) :=
    fun i => by
      change Quasicategory (nerve (F.obj i).Elementsᵒᵖ)
      infer_instance
  exact kanDiagramFunctorIsoOfPointwise
    (F := ⟨_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamily ((_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.simplexElementsNerveDiagram F) ⋙ SSet.opFunctor), trivial⟩)
    (G := ⟨_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamily (F ⋙ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.functor), trivial⟩)
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamilyMap e.hom)
    (fun i => _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamilyMap_isQCatEquivalence e.hom
      (fun i => (qCatEquivalenceOfIso (e.app i)).isQCatEquivalence.isWeakHomotopyEquivalence) i)

/-- 元の終端augmentationの全自然変換。 -/
def simplexElementsOppositeAugmentation : F ⋙ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.functor ⟶ F :=
  Functor.whiskerLeft F _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.augmentation

/-- 同じ元の終端augmentationの全成分の弱同値性。 -/
lemma simplexElementsOppositeAugmentation_weak (i : I) :
    IsWeakHomotopyEquivalence ((_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.simplexElementsOppositeAugmentation F).app i) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.augmentation_localized_isIso (F.obj i))

/-- 元の反対要素圏の全augmentationのKan化による全関手同型。 -/
def simplexElementsOppositeAugmentationIso :
    FunctorIso (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamilyCoherent (F ⋙ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.functor))
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamilyCoherent F) :=
  kanDiagramFunctorIsoOfPointwise
    (F := ⟨_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamily (F ⋙ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.functor), trivial⟩)
    (G := ⟨_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamily F, trivial⟩)
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamilyMap (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.simplexElementsOppositeAugmentation F))
    (fun i => _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamilyMap_isQCatEquivalence _ (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.simplexElementsOppositeAugmentation_weak F) i)

/-- 元の全要素圏の係数を、同じ反転同型と元の終端augmentationへ接続する。 -/
def simplexElementsKanAugmentationIso :
    FunctorIso (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamilyCoherent (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.simplexElementsNerveDiagram F))
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamilyCoherent F) :=
  (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamilyOppositeComparisonIso (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.simplexElementsNerveDiagram F)).trans
    ((_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.simplexElementsOppositeNerveKanIso F).trans (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.simplexElementsOppositeAugmentationIso F))
end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
