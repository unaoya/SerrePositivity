module
public import SerrePositivity.KST.SConstruction.ExInfinityPointedEnrichedFunctor
public import SerrePositivity.KST.SConstruction.PointedKanStrictExtension
public import SerrePositivity.KST.SConstruction.PointedExtensionHomotopy
public import SerrePositivity.KST.Spectra.PostMappingIsomorphism
public import SerrePositivity.KST.Spectra.PointedHomotopyClasses

/-! # 元の SOA と同じ Ex∞ の前向き Kan 比較
概要：同じ元の点つき対象の二つの Kan 模型を全基点 π 同型で比較する。
方針：anodyne 単位を厳密に延長し、二つの延長の同じ成分を使う。
規約：SOA の豊穣性は仮定しない。使われ方：元の dgK と厳密豊穣 BF K の比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.SimplicialModel

/-- 元の loop の Kan 性を basedHom 関手の対象の型でも保持する。 -/
local instance pointedSOAExInfinityLoop_kanComplex (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] :
    KanComplex ((PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u}).obj Y).right :=
  loopSpace_kanComplex Y

/-- 同じ元の対象の SOA Kan 模型から Ex∞ Kan 模型への前向き比較。 -/
def pointedSOAExInfinityComparison (X : PointedSSetObject.{u}) :
    PointedKanReplacement.obj X.obj ⟶ (exInfinityPointedKanEnrichedFunctor.obj X).obj :=
  pointedKanStrictExtension (exInfinityPointedUnit X)

/-- 同じ比較は元の Ex∞ 単位を厳密に回収する。 -/
lemma pointedSOAExInfinityComparison_unit (X : PointedSSetObject.{u}) :
    PointedKanReplacement.unit.app X.obj ≫ pointedSOAExInfinityComparison X =
      exInfinityPointedUnit X :=
  pointedKanStrictExtension_fac _

/-- 元の単位の厳密延長で得た同じ比較は全基点 π 同型。 -/
lemma pointedSOAExInfinityComparison_piIsomorphism (X : PointedSSetObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (pointedSOAExInfinityComparison X).right :=
  pointedKanStrictExtension_piIsomorphism _
    ((Localization.inverts AnodyneHomotopy.anodyneQ anodyneExtensions) _
      (exInfinityPointedUnit_anodyne X))

/-- 同じ二つの Kan 模型の loop 比較も全基点 π 同型。 -/
lemma pointedSOAExInfinityComparison_loop_piIsomorphism (X : PointedSSetObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
      ((PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u}).map
        (pointedSOAExInfinityComparison X)).right :=
  PointedMapping.post_piIsomorphism PointedSimplicialSet.circle _
    (pointedSOAExInfinityComparison_piIsomorphism X)

/-- 同じ Ex∞ 単位は元の通常の点つき射に関して厳密に自然。 -/
lemma exInfinityPointedUnit_naturality {X Y : PointedSSetObject.{u}} (f : X ⟶ Y) :
    exInfinityPointedUnit X ≫ (exInfinityPointedKanMap f).hom =
      (show X.obj ⟶ Y.obj from f) ≫ exInfinityPointedUnit Y := by
  apply Under.UnderMorphism.ext
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.naturality (show X.obj ⟶ Y.obj from f).right).symm

/-- 同じ前向き Kan 比較は、通常の点つき射に関して基点固定成分で自然。 -/
lemma pointedSOAExInfinityComparison_naturality_component
    {X Y : PointedSSetObject.{u}} (f : X ⟶ Y) :
    PointedMapping.componentOf
        (pointedSOAExInfinityComparison X ≫ (exInfinityPointedKanMap f).hom) =
      PointedMapping.componentOf
        (PointedKanReplacement.map (show X.obj ⟶ Y.obj from f) ≫
          pointedSOAExInfinityComparison Y) := by
  obtain ⟨e⟩ := pointedExtensions_nonempty_mappingEdge
    (PointedKanReplacement.unit.app X.obj) (PointedKanReplacement.unit_anodyne X.obj)
    ((show X.obj ⟶ Y.obj from f) ≫ exInfinityPointedUnit Y)
    (pointedSOAExInfinityComparison X ≫ (exInfinityPointedKanMap f).hom)
    (PointedKanReplacement.map (show X.obj ⟶ Y.obj from f) ≫
      pointedSOAExInfinityComparison Y)
    (by erw [← Category.assoc, pointedSOAExInfinityComparison_unit,
      exInfinityPointedUnit_naturality]) (by
      erw [← Category.assoc, ← PointedKanReplacement.unit.naturality,
        Category.assoc, pointedSOAExInfinityComparison_unit]
      rfl)
  exact SSet.π₀.sound e

end SerrePositivity.KST.SConstruction
