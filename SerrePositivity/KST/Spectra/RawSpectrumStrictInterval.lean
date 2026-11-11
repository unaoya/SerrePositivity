module

public import SerrePositivity.KST.Spectra.SequenceIntervalRectification
public import SerrePositivity.KST.Spectra.RawSpectrumParameterRestriction
public import SerrePositivity.KST.Spectra.KanSequenceCategory

/-!
概要：両端を固定した厳密な区間列を、元の全 Hom の同じ両端を持つ実区間へ戻す。
方針：cotensor 交換で全パラメータ族を回収し、両端は元の列射の点として計算する。
規約：各段のホモトピーを寄せ集めない。使われ方：元の全 Hom のホモトピーの構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra

/-- 自由な点つき区間を忘れた族の面は、指定した同じ端点の族。 -/
lemma freeIntervalFamily_face {E : PointedSimplicialSet.{u}} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeInterval.{u} ⟶ E)
    (i : Fin 2) :
    stdSimplex.δ i ≫ PointedObject.adjoinHomEquiv (Δ[1] : SSet.{u}) E F =
      PointedSimplicialSet.deltaZeroUnitIso.{u}.hom ≫
        PointedSimplicialSet.unitUnderlyingHom E (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint i ≫ F) := by
  change stdSimplex.δ.{u} i ≫ coprod.inl ≫ F.right =
    PointedSimplicialSet.deltaZeroUnitIso.{u}.hom ≫ coprod.inl ≫
      (coprod.map PointedSimplicialSet.deltaZeroUnitIso.{u}.inv (𝟙 (𝟙_ SSet.{u})) ≫
        coprod.map (stdSimplex.δ.{u} i) (𝟙 (𝟙_ SSet.{u}))) ≫ F.right
  simp only [Category.assoc, coprod.inl_map_assoc, Iso.hom_inv_id_assoc]

namespace RawSpectrumMapping
variable (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
  {f g : KanSequence.Hom X.toKanSequence Y} (H : KanSequence.StrictInterval f g)

/-- 同じ全列区間を、元の全 Hom の自由区間パラメータ族として回収する。 -/
def strictIntervalFamily : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeInterval.{u} ⟶ pointedSpace X Y :=
  parameterFamily X Y _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeInterval H.hom

/-- 元の全 Hom 内の始点は、指定した厳密な列射の点そのもの。 -/
lemma strictIntervalFamily_start :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint 1 ≫ strictIntervalFamily X Y H = homPoint X Y f := by
  rw [strictIntervalFamily, parameterFamily_endpoint]
  congr 1
  apply KanSequence.Hom.ext_app
  exact H.start

/-- 元の全 Hom 内の終点も、指定した厳密な列射の点そのもの。 -/
lemma strictIntervalFamily_finish :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint 0 ≫ strictIntervalFamily X Y H = homPoint X Y g := by
  rw [strictIntervalFamily, parameterFamily_endpoint]
  congr 1
  apply KanSequence.Hom.ext_app
  exact H.finish

/-- 同じ厳密な全列区間から、元の全 Hom の実際の辺を構成する。 -/
def strictIntervalEdge : (pointedSpace X Y).right.Edge
    (PointedSimplicialSet.unitVertexEquiv _ (homPoint X Y f))
    (PointedSimplicialSet.unitVertexEquiv _ (homPoint X Y g)) := by
  let r := PointedObject.adjoinHomEquiv (Δ[1] : SSet.{u}) (pointedSpace X Y)
    (strictIntervalFamily X Y H)
  refine SSet.Edge.mk (SSet.yonedaEquiv r) ?_ ?_
  · rw [← stdSimplex.yonedaEquiv_δ_comp]
    change SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ _) = _
    rw [freeIntervalFamily_face, strictIntervalFamily_start]
    rfl
  · rw [← stdSimplex.yonedaEquiv_δ_comp]
    change SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ _) = _
    rw [freeIntervalFamily_face, strictIntervalFamily_finish]
    rfl

include H in
/-- 同じ全列区間の両端は、元の全 Hom の同じ連結成分に属する。 -/
lemma strictInterval_component :
    π₀.mk (PointedSimplicialSet.unitVertexEquiv _ (homPoint X Y f)) =
      π₀.mk (PointedSimplicialSet.unitVertexEquiv _ (homPoint X Y g)) :=
  π₀.sound (strictIntervalEdge X Y H)

end RawSpectrumMapping
end SerrePositivity.KST.Spectra
