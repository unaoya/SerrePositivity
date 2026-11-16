module
public import SerrePositivity.EInfinity.FrameHom.KanHomFamilyOpposite
public import SerrePositivity.EInfinity.FrameHom.SimplexTerminalEquivalence

/-!
概要：元の全要素圏のKan化を、同じ反対要素圏の終端augmentationへつなぐ。
方針：既存のnerve反転同型と全augmentationの自然性・反転性を合成する。
規約：底と全作用素を保ち、固定始域のroofとの等式は別に照合する。
使われ方：両変数のsource frameの全係数の規約の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory SSet
open SerrePositivity.SimplicialModel
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
variable {I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})

/-- 同じ全係数の元の要素圏のnerveの図式。 -/
abbrev simplexElementsNerveDiagram : I ⥤ SSet.{u} := F ⋙ SimplexNerve.functor

/-- 元のnerveの反転同型を同じ全係数へ前合成する。 -/
def simplexElementsOppositeNerveIso :
    (simplexElementsNerveDiagram F) ⋙ SSet.opFunctor ≅ F ⋙ SimplexTerminalNerve.functor :=
  Functor.isoWhiskerLeft F SimplexTerminalNerve.oppositeIso.symm

/-- 同じ元のnerve反転同型のKan化。 -/
def simplexElementsOppositeNerveKanIso :
    FunctorIso (kanHomFamilyCoherent ((simplexElementsNerveDiagram F) ⋙ SSet.opFunctor))
      (kanHomFamilyCoherent (F ⋙ SimplexTerminalNerve.functor)) := by
  let e := simplexElementsOppositeNerveIso F
  have : ∀ i, Quasicategory (((simplexElementsNerveDiagram F) ⋙ SSet.opFunctor).obj i) :=
    fun i => by
      change Quasicategory (nerve (F.obj i).Elements).op
      infer_instance
  have : ∀ i, Quasicategory ((F ⋙ SimplexTerminalNerve.functor).obj i) :=
    fun i => by
      change Quasicategory (nerve (F.obj i).Elementsᵒᵖ)
      infer_instance
  exact kanDiagramFunctorIsoOfPointwise
    (F := ⟨kanHomFamily ((simplexElementsNerveDiagram F) ⋙ SSet.opFunctor), trivial⟩)
    (G := ⟨kanHomFamily (F ⋙ SimplexTerminalNerve.functor), trivial⟩)
    (kanHomFamilyMap e.hom)
    (fun i => kanHomFamilyMap_isQCatEquivalence e.hom
      (fun i => (qCatEquivalenceOfIso (e.app i)).isQCatEquivalence.isWeakHomotopyEquivalence) i)

/-- 元の終端augmentationの全自然変換。 -/
def simplexElementsOppositeAugmentation : F ⋙ SimplexTerminalNerve.functor ⟶ F :=
  Functor.whiskerLeft F SimplexTerminalNerve.augmentation

/-- 同じ元の終端augmentationの全成分の弱同値性。 -/
lemma simplexElementsOppositeAugmentation_weak (i : I) :
    IsWeakHomotopyEquivalence ((simplexElementsOppositeAugmentation F).app i) :=
  AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (SimplexTerminalNerve.augmentation_localized_isIso (F.obj i))

/-- 元の反対要素圏の全augmentationのKan化による全関手同型。 -/
def simplexElementsOppositeAugmentationIso :
    FunctorIso (kanHomFamilyCoherent (F ⋙ SimplexTerminalNerve.functor))
      (kanHomFamilyCoherent F) :=
  kanDiagramFunctorIsoOfPointwise
    (F := ⟨kanHomFamily (F ⋙ SimplexTerminalNerve.functor), trivial⟩)
    (G := ⟨kanHomFamily F, trivial⟩)
    (kanHomFamilyMap (simplexElementsOppositeAugmentation F))
    (fun i => kanHomFamilyMap_isQCatEquivalence _ (simplexElementsOppositeAugmentation_weak F) i)

/-- 元の全要素圏の係数を、同じ反転同型と元の終端augmentationへ接続する。 -/
def simplexElementsKanAugmentationIso :
    FunctorIso (kanHomFamilyCoherent (simplexElementsNerveDiagram F))
      (kanHomFamilyCoherent F) :=
  (kanHomFamilyOppositeComparisonIso (simplexElementsNerveDiagram F)).trans
    ((simplexElementsOppositeNerveKanIso F).trans (simplexElementsOppositeAugmentationIso F))
end SerrePositivity.EInfinity.FrameHom
