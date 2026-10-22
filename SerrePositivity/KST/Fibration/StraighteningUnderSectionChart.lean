module
public import SerrePositivity.KST.Fibration.StraighteningBaseChangeChartComponents
public import SerrePositivity.KST.Fibration.TransportUnderSectionPoint

/-! # 元の初頂点 under 比較を、同じ切断比較と元の under 制限成分に分解する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w v' w'
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {B : SSet.{u}}

private lemma normalizeComposition {C : Type v} [Category.{w} C]
    {a b c b' c' : C} (l : a ≅ b) (e : b ≅ c) (hb : b = b') (hc : c = c') :
    F2.isoNormalizeEndpoints (l ≪≫ e) rfl hc =
      F2.isoNormalizeEndpoints l rfl hb ≪≫ F2.isoNormalizeEndpoints e hb hc := by
  subst b' c'
  simp only [F2.isoNormalizeEndpoints, eqToIso_refl, Iso.refl_symm, Iso.refl_trans,
    Iso.trans_refl]

private lemma mapNormalizeComposition {C : Type v} [Category.{w} C]
    {Z : Type v'} [Category.{w'} Z] (F : C ⥤ Z) {a b c : C} {b' c' : Z}
    (l : a ≅ b) (e : b ≅ c) (d : a ≅ c) (hd : d = l ≪≫ e)
    (hb : F.obj b = b') (hc : F.obj c = c') :
    F2.isoNormalizeEndpoints (F.mapIso d) rfl hc =
      F2.isoNormalizeEndpoints (F.mapIso l) rfl hb ≪≫
        F2.isoNormalizeEndpoints (F.mapIso e) hb hc := by
  subst d
  rw [Functor.mapIso_trans]
  exact normalizeComposition _ _ hb hc

/-- 元の初頂点 under 共同同型の二重成分を、同じ under 切断空間へ表示する。 -/
def straighteningFirstVertexUnderChart (X : LeftFibrationObject B)
    (c : TransportSimplexCategory B) :=
  F2.isoNormalizeEndpoints
    (VertexIso.map (leftStraighteningSectionJointDiagram_underIso B)
      (doubleFunctorEvaluation (Y := SpaceInfinity.{u})
        (ULift.up (nerveVertex c)) (coherentNerveVertex X))) rfl
    (congrArg HomotopyCategory.mk
      (relativeSectionDiagramInfinity_double_vertex (transportSimplexUnderDomains B) X c))

/-- 表示変更後も、元の under 共同同型の同じ指定二重成分を保持する。 -/
theorem straighteningFirstVertexUnderChart_heq_doubleMap
    (X : LeftFibrationObject B) (c : TransportSimplexCategory B) :
    HEq (straighteningFirstVertexUnderChart X c)
      (VertexIso.map (leftStraighteningSectionJointDiagram_underIso B)
        (doubleFunctorEvaluation (Y := SpaceInfinity.{u})
          (ULift.up (nerveVertex c)) (coherentNerveVertex X))) := by
  unfold straighteningFirstVertexUnderChart F2.isoNormalizeEndpoints
  exact F2.iso_endpoints_heq _ _ _

/-- 同じ元の under 成分は、同じ初頂点の切断比較と同じ実制限成分の合成。 -/
theorem straighteningFirstVertexUnderChart_factor
    (X : LeftFibrationObject B) (c : TransportSimplexCategory B) :
    straighteningFirstVertexUnderChart X c =
      straighteningFirstVertexSectionChart X c ≪≫ transportUnderJointComponentIso X c := by
  let T := doubleFunctorEvaluation
    (K := (SSet.uliftFunctor.{u + 1, u}).obj (nerve (TransportSimplexCategory B)))
    (A := LeftFibrationInfinity B) (Y := SpaceInfinity.{u})
    (ULift.up (nerveVertex c)) (coherentNerveVertex X)
  exact mapNormalizeComposition (hoFunctor.map T).toFunctor
    (leftStraighteningSectionJointDiagram_restrictIso B) (transportSimplexUnderJointIso B)
    (leftStraighteningSectionJointDiagram_underIso B) rfl
    (congrArg HomotopyCategory.mk
      (relativeSectionDiagramInfinity_double_vertex (transportSimplexDomainFunctor B) X c))
    (congrArg HomotopyCategory.mk
      (relativeSectionDiagramInfinity_double_vertex (transportSimplexUnderDomains B) X c))

/-- 同じ初頂点比較で表示した元の切断点は、元の under 比較で同じ実制限像へ移る。 -/
theorem straighteningFirstVertexUnderChart_pointHom
    (X : LeftFibrationObject B) (c : TransportSimplexCategory B)
    (v : (((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).obj c).obj X).obj
      _⦋0⦌) :
    cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      (((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).obj c).obj X)).symm v) ≫
      (straighteningFirstVertexSectionChart X c).inv ≫
        (straighteningFirstVertexUnderChart X c).hom =
    cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      (((relativeSectionEnrichedDiagram (transportSimplexUnderDomains B)).obj c).obj X)).symm
        ((relativeFunctorOverPre X.val.hom
          ((transportSimplexUnderDomainTransformation B).app (Opposite.op c))).app
            (Opposite.op ⦋0⦌) v)) := by
  rw [straighteningFirstVertexUnderChart_factor]
  simp only [Iso.trans_hom, Iso.inv_hom_id_assoc]
  exact transportUnderJointComponentIso_pointHom X c v

end SerrePositivity.KST.Fibration
