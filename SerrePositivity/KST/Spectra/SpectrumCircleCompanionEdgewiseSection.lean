module

public import SerrePositivity.KST.Spectra.SpectrumCircleCompanionBKSection
public import SerrePositivity.KST.Spectra.SpectrumCircleCompanionConePoint
public import SerrePositivity.KST.Spectra.LoopEdgewiseSectionFaces
public import SerrePositivity.InfinityCategories.HomotopyLimits.SectionsDiagramNaturality

/-!
概要：元の companion の Hom–BK 点を共通解像の全切断へ持ち上げ、loop 係数へ移す。
方針：右 end 射影の切断式を uncurry し、係数同型と右射影の自然性を使う。
規約：元の右切断と中央 Hom を保持。使われ方：反転した実際の錐の三単体の符号計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance companionEdgewiseSectionSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
local instance companionEdgewiseSectionHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := mappingSpace_kanComplex X Y

/-- 元の companion 点を、同じ右切断で共通 edgewise end へ持ち上げる射。 -/
def circleCompanionBKEdgewisePointMap (z : Sp.{u} _⦋0⦌) :=
  circleCompanionBKEndPointMap z ≫ edgewiseEndRightSection
    (simplicialHomDiagram
      (pointLoopDiagram (nativeCotensorInput PointedSimplicialSet.circle z).val)
      (cotensor PointedSimplicialSet.circle
        (nativeCotensorInput PointedSimplicialSet.circle z).val))

/-- 共通解像へ持ち上げた元の点の右射影は、元の companion 点そのもの。 -/
lemma circleCompanionBKEdgewisePointMap_right (z : Sp.{u} _⦋0⦌) :
    circleCompanionBKEdgewisePointMap z ≫ weightedSectionsMap
      (bousfieldKanWeight (AsSmall.{u} WalkingCospan))
      (diagramEdgewiseRight (simplicialHomDiagram
        (pointLoopDiagram (nativeCotensorInput PointedSimplicialSet.circle z).val)
        (cotensor PointedSimplicialSet.circle
          (nativeCotensorInput PointedSimplicialSet.circle z).val))) =
      circleCompanionBKEndPointMap z := by
  rw [circleCompanionBKEdgewisePointMap, Category.assoc,
    edgewiseEndRightSection_projection, Category.comp_id]

/-- 元の Hom 係数の共通解像上での、companion の全 BK 重みの切断。 -/
def circleCompanionBKEdgewiseSection (z : Sp.{u} _⦋0⦌) :=
  (ρ_ (bousfieldKanWeight (AsSmall.{u} WalkingCospan))).inv ≫
    weightedSectionsUncurry (circleCompanionBKEdgewisePointMap z)

/-- 元の共通解像切断全体の右射影は、元の companion の全切断。 -/
lemma circleCompanionBKEdgewiseSection_right (z : Sp.{u} _⦋0⦌) :
    circleCompanionBKEdgewiseSection z ≫ diagramEdgewiseRight
      (simplicialHomDiagram
        (pointLoopDiagram (nativeCotensorInput PointedSimplicialSet.circle z).val)
        (cotensor PointedSimplicialSet.circle
          (nativeCotensorInput PointedSimplicialSet.circle z).val)) =
      circleCompanionBKSection z := by
  rw [circleCompanionBKEdgewiseSection, Category.assoc,
    ← weightedSectionsUncurry_postcomp, circleCompanionBKEdgewisePointMap_right]
  rfl

/-- 同じ切断を、中央の Hom を恒等に保つ係数同型で loop 係数へ移す。 -/
def circleCompanionBKEdgewiseLoopSection (z : Sp.{u} _⦋0⦌) :
    bousfieldKanWeight (AsSmall.{u} WalkingCospan) ⟶
      loopCoefficient (circleEvaluationPointedHom z) ⋙ edgewiseSubdivisionFunctor :=
  circleCompanionBKEdgewiseSection z ≫ Functor.whiskerRight
    (pointLoopHomCoefficientIso
      (cotensor PointedSimplicialSet.circle
        (nativeCotensorInput PointedSimplicialSet.circle z).val)
      (nativeCotensorInput PointedSimplicialSet.circle z).val).hom
    edgewiseSubdivisionFunctor

/-- 係数同型は中央では恒等なので、元の共通解像の単体を変えない。 -/
lemma circleCompanionBKEdgewiseLoopSection_central (z : Sp.{u} _⦋0⦌) :
    (circleCompanionBKEdgewiseLoopSection z).app (AsSmall.up.obj .one) =
      (circleCompanionBKEdgewiseSection z).app (AsSmall.up.obj .one) := by
  change _ ≫ edgewiseSubdivisionFunctor.map (𝟙 _) = _
  rw [edgewiseSubdivisionFunctor.map_id, Category.comp_id]

/-- loop 係数へ移した切断の右射影も、元の companion 切断を厳密に保つ。 -/
lemma circleCompanionBKEdgewiseLoopSection_right (z : Sp.{u} _⦋0⦌) :
    circleCompanionBKEdgewiseLoopSection z ≫
      diagramEdgewiseRight (loopCoefficient (circleEvaluationPointedHom z)) =
    circleCompanionBKSection z ≫ (pointLoopHomCoefficientIso
      (cotensor PointedSimplicialSet.circle
        (nativeCotensorInput PointedSimplicialSet.circle z).val)
      (nativeCotensorInput PointedSimplicialSet.circle z).val).hom := by
  rw [circleCompanionBKEdgewiseLoopSection, Category.assoc]
  have hn : Functor.whiskerRight (pointLoopHomCoefficientIso
      (cotensor PointedSimplicialSet.circle
        (nativeCotensorInput PointedSimplicialSet.circle z).val)
      (nativeCotensorInput PointedSimplicialSet.circle z).val).hom
      edgewiseSubdivisionFunctor ≫
        diagramEdgewiseRight (loopCoefficient (circleEvaluationPointedHom z)) =
      diagramEdgewiseRight (simplicialHomDiagram
        (pointLoopDiagram (nativeCotensorInput PointedSimplicialSet.circle z).val)
        (cotensor PointedSimplicialSet.circle
          (nativeCotensorInput PointedSimplicialSet.circle z).val)) ≫
        (pointLoopHomCoefficientIso
          (cotensor PointedSimplicialSet.circle
            (nativeCotensorInput PointedSimplicialSet.circle z).val)
          (nativeCotensorInput PointedSimplicialSet.circle z).val).hom := by
    apply NatTrans.ext
    funext i
    exact edgewiseRight_naturality _
  rw [hn, ← Category.assoc, circleCompanionBKEdgewiseSection_right]

/-- 右射影後の中央の切断は、元の companion 円の評価。 -/
lemma circleCompanionBKEdgewiseLoopSection_right_central (z : Sp.{u} _⦋0⦌) :
    (circleCompanionBKEdgewiseLoopSection z).app (AsSmall.up.obj .one) ≫
      edgewiseRight (circleEvaluationPointedHom z).right =
        circleBKParameter.{u} ≫ (circleEvaluationCompanionCircleMap z).right := by
  have h := congrArg (fun η ↦ η.app (AsSmall.up.obj WalkingCospan.one))
    (circleCompanionBKEdgewiseLoopSection_right z)
  change _ = (circleCompanionBKSection z).app (AsSmall.up.obj .one) ≫ 𝟙 _ at h
  rw [Category.comp_id, circleCompanionBKSection_central] at h
  exact h

end SerrePositivity.KST.Spectra.OmegaSpectrum
