module
public import SerrePositivity.KST.SConstruction.PointedKanDiagramEquivalences
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomotopyComposition

/-! # Kan 延長を図式全体の coherent な変換として構成する
概要：R→L の元の自然変換を、Kan(R)→L の全射列に自然な変換へ移す。
方針：Kan 置換後の厳密な変換と、Kan な標的の単位の図式全体の逆を合成する。
規約：両辺を保つ関手空間の実三角形も保持する。元の厳密な延長との比較は別工程。
使われ方：構造射の延長側の高次整合性と、比較逆射との合成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 任意の点つき図式の Kan 置換に関する全対象の Kan 性。 -/
lemma pointedDiagramReplacement_isKan {I : Type u} [SmallCategory I]
    (F : I ⥤ PointedSimplicialSet.{u}) (i : I) :
    KanComplex ((F ⋙ PointedKanReplacement.functor).obj i).right :=
  PointedKanReplacement.obj_kanComplex (F.obj i)

/-- Kan な図式の置換単位は、coherent 図式全体の関手同型。 -/
def pointedKanDiagramUnitIso {I : Type u} [SmallCategory I]
    (F : I ⥤ PointedSimplicialSet.{u}) (hF : ∀ i, KanComplex (F.obj i).right) :=
  pointedKanDiagramFunctorIso hF (pointedDiagramReplacement_isKan F)
    (Functor.whiskerLeft F PointedKanReplacement.unit)
    (fun i => by
      let : KanComplex (F.obj i).right := hF i
      exact PointedKanReplacement.unit_piIsomorphism (F.obj i))

/-- 図式全体の置換単位の逆の、全入力単体にわたる実円柱。 -/
def pointedKanDiagramUnitInverseHomotopy {I : Type u} [SmallCategory I]
    (F : I ⥤ PointedSimplicialSet.{u}) (hF : ∀ i, KanComplex (F.obj i).right) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.simplicialHomotopy (pointedKanDiagramUnitIso F hF).symm

/-- 元の自然変換を Kan 置換した、図式全体の実円柱。 -/
def pointedKanReplacedNatTransHomotopy {I : Type u} [SmallCategory I]
    {R L : I ⥤ PointedSimplicialSet.{u}} (θ : R ⟶ L) :=
  pointedKanDiagramHomotopy (pointedDiagramReplacement_isKan R)
    (pointedDiagramReplacement_isKan L) (Functor.whiskerRight θ PointedKanReplacement.functor)

/-- Kan な標的への自然変換は、源の Kan 置換からの coherent な変換へ延長できる。 -/
def pointedKanDiagramExtensionHomotopy {I : Type u} [SmallCategory I]
    {R L : I ⥤ PointedSimplicialSet.{u}} (hL : ∀ i, KanComplex (L.obj i).right)
    (θ : R ⟶ L) :
    SSet.Homotopy
      (pointedKanCoherentDiagram (R ⋙ PointedKanReplacement.functor)
        (pointedDiagramReplacement_isKan R)) (pointedKanCoherentDiagram L hL) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomotopyComposite (pointedKanReplacedNatTransHomotopy θ)
    (pointedKanDiagramUnitInverseHomotopy L hL)

/-- coherent な延長と元の二つの因子を同時に回収する関手空間の実三角形。 -/
def pointedKanDiagramExtensionTriangle {I : Type u} [SmallCategory I]
    {R L : I ⥤ PointedSimplicialSet.{u}} (hL : ∀ i, KanComplex (L.obj i).right)
    (θ : R ⟶ L) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle (pointedKanReplacedNatTransHomotopy θ)
      (pointedKanDiagramUnitInverseHomotopy L hL) (pointedKanDiagramExtensionHomotopy hL θ) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomotopyCompositeTriangle _ _

end SerrePositivity.KST.SConstruction
