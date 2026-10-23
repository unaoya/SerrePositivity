module

public import SerrePositivity.InfinityCategories.F2.Ind.StrictRightFibrationDiagramColimit
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.RelativeEdgewiseRightFibration

/-!
概要：元の right fibration 図式の twisted arrow と相対右端比較を全添字で自然に組む。
方針：元の底上の作用を引き戻しに写し、twisted arrow の両射影で自然性を検査。
規約：個別の切断は選ばない。使われ方：大域密度の指定変換を同じ全族で構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} {I : Type u} [SmallCategory I]
  (F : I ⥤ RightFibrationObject C)

/-- 元の全空間の終点を保つ、底の twisted arrow の引き戻しの通常図式。 -/
def strictRightTwistedElementsDiagram : I ⥤ SSet.{u} where
  obj i := pullback (edgewiseRight C) (F.obj i).val.hom
  map {i j} f := pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ (F.map f).left) (by
      rw [Category.assoc, Over.w]
      exact pullback.condition)
  map_id i := by
    apply pullback.hom_ext <;> simp
    change _ ≫ 𝟙 _ = _
    exact Category.comp_id _
  map_comp f g := by
    apply pullback.hom_ext <;> simp [Category.assoc]
    exact (Category.assoc _ _ _).symm

/-- 元の全空間の twisted arrow を、同じ通常の添字で動かす図式。 -/
def strictRightTwistedTotalDiagram : I ⥤ SSet.{u} :=
  rightFibrationTotalDiagram F ⋙ edgewiseSubdivisionFunctor

/-- 相対右端比較は、元の図式の全ての作用に厳密に自然。 -/
def strictRightTwistedComparison :
    strictRightTwistedTotalDiagram F ⟶ strictRightTwistedElementsDiagram F where
  app i := relativeEdgewiseRightComparison (F.obj i).val.hom
  naturality i j f := by
    apply pullback.hom_ext
    · simp only [Category.assoc, relativeEdgewiseRightComparison_fst,
        strictRightTwistedElementsDiagram, pullback.lift_fst]
      change edgewiseSubdivisionFunctor.map (F.map f).left ≫
        edgewiseSubdivisionFunctor.map (F.obj j).val.hom =
          edgewiseSubdivisionFunctor.map (F.obj i).val.hom
      rw [← Functor.map_comp, Over.w]
    · simp only [Category.assoc, relativeEdgewiseRightComparison_snd,
        strictRightTwistedElementsDiagram, pullback.lift_snd]
      change edgewiseSubdivisionMap (F.map f).left ≫ edgewiseRight _ =
        relativeEdgewiseRightComparison (F.obj i).val.hom ≫
          (pullback.snd _ _ ≫ (F.map f).left)
      rw [← Category.assoc, relativeEdgewiseRightComparison_snd, edgewiseRight_naturality]

/-- 同じ自然比較の全成分は、元の right fibration の自明 Kan 比較。 -/
instance strictRightTwistedComparison_trivialKanFibration (i : I) :
    TrivialKanFibration ((strictRightTwistedComparison F).app i) :=
  relativeEdgewiseRightComparison_trivialKanFibration (F.obj i).val.hom

end SerrePositivity.InfinityCategories.F2.Ind
