module
public import SerrePositivity.KST.SConstruction.ObjectTriangulatedFunctor
public import SerrePositivity.KST.SConstruction.ObjectBoundaryWeakEquivalence
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanActualHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanTestDetection

/-! # 三角圏 K₀ の nerve 値写像の元の境界商への移送
概要：元の object S の三角圏 K₀ 値写像を元の境界商へ移し、実際のホモトピーで回収する。
方針：既存の比較の局所化同値と Kan 値のホモトピー類の全単射を使う。
規約：object S₀ の離散頂点を潰した商は使わない。使われ方：K₀ 比較の逆向き写像。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits SSet
open SerrePositivity.SimplicialModel

/-- 元の object S の K₀ 値写像は、元の境界商上の写像で実際のホモトピーまで回収できる。 -/
lemma exists_rawBoundaryTriangulatedMap (X : StableModel.{u}) :
    ∃ f : (boundaryReducedRealization 0 X).right ⟶
        nerve (AsSmall.{u} (triangulatedKZeroDelooping X)),
      Nonempty (SSet.Homotopy (objectRawBoundaryComparison X ≫ f)
        (objectTriangulatedNerveMap X)) := by
  let T := nerve (AsSmall.{u} (triangulatedKZeroDelooping X))
  have hT : modelCategoryQuillen.J.rlp (terminal.from T) :=
    (modelCategoryQuillen.fibration_iff _).mp inferInstance
  obtain ⟨a, ha⟩ := (KanTestDetection.tests_of_anodyneQ_isIso
    (objectRawBoundaryComparison X) (objectRawBoundaryComparison_localized_isIso X) T hT).surjective
      (HomotopyClasses.mk (objectTriangulatedNerveMap X))
  obtain ⟨f, rfl⟩ := Quot.exists_rep a
  change HomotopyClasses.mk (objectRawBoundaryComparison X ≫ f) =
    HomotopyClasses.mk (objectTriangulatedNerveMap X) at ha
  exact ⟨f, KanActualHomotopy.of_class_eq hT ha⟩

/-- 元の全零境界商から三角圏 K₀ の一対象亜群の nerve への実際の写像。 -/
def rawBoundaryTriangulatedMap (X : StableModel.{u}) :
    (boundaryReducedRealization 0 X).right ⟶
      nerve (AsSmall.{u} (triangulatedKZeroDelooping X)) :=
  Classical.choose (exists_rawBoundaryTriangulatedMap X)

/-- 選んだ境界商上の写像の元の object S への制限は、元の K₀ 値写像と実際にホモトピック。 -/
def rawBoundaryTriangulatedHomotopy (X : StableModel.{u}) :
    SSet.Homotopy (objectRawBoundaryComparison X ≫ rawBoundaryTriangulatedMap X)
      (objectTriangulatedNerveMap X) :=
  Classical.choice (Classical.choose_spec (exists_rawBoundaryTriangulatedMap X))

/-- 元の境界商上の K₀ 値写像を既存の Kan 単位に沿って厳密に延長できる。 -/
lemma exists_boundaryKanTriangulatedMap (X : StableModel.{u}) :
    ∃ f : ((boundaryKanRealizationFunctor 0).obj X).right ⟶
        nerve (AsSmall.{u} (triangulatedKZeroDelooping X)),
      (Spectra.PointedKanReplacement.unit.app (boundaryReducedRealization 0 X)).right ≫ f =
        rawBoundaryTriangulatedMap X := by
  let T := nerve (AsSmall.{u} (triangulatedKZeroDelooping X))
  let i := (Spectra.PointedKanReplacement.unit.app (boundaryReducedRealization 0 X)).right
  have : HasLiftingProperty i (terminal.from T) :=
    (Spectra.PointedKanReplacement.unit_anodyne (boundaryReducedRealization 0 X)) _
      (by rw [← HomotopicalAlgebra.fibration_iff]; infer_instance)
  let sq : CommSq (rawBoundaryTriangulatedMap X) i (terminal.from T)
      (terminal.from ((boundaryKanRealizationFunctor 0).obj X).right) :=
    ⟨terminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- 既存の一重 S の Kan 境界から三角圏 K₀ の nerve への実際の延長。 -/
def boundaryKanTriangulatedMap (X : StableModel.{u}) :
    ((boundaryKanRealizationFunctor 0).obj X).right ⟶
      nerve (AsSmall.{u} (triangulatedKZeroDelooping X)) :=
  Classical.choose (exists_boundaryKanTriangulatedMap X)

/-- 既存の Kan 境界上の写像は、元の境界商の写像を厳密に回収する。 -/
lemma boundaryKanTriangulatedMap_unit (X : StableModel.{u}) :
    (Spectra.PointedKanReplacement.unit.app (boundaryReducedRealization 0 X)).right ≫
      boundaryKanTriangulatedMap X = rawBoundaryTriangulatedMap X :=
  Classical.choose_spec (exists_boundaryKanTriangulatedMap X)

end SerrePositivity.KST.SConstruction
