module

public import SerrePositivity.AlgebraicGeometry.CoefficientModelFiltered
public import Mathlib.CategoryTheory.Limits.Comma

/-!
概要：全模型の両辺と元の構造写像を、実際の環の図式・cocone にまとめる。
方針：模型の射の圏から Arrow と両射影へ送り、小さい添字へ移す。
規約：元の g と同じ cocone を保つ。余極限性は別に証明する。
使われ方：B03・B04 の全模型と被覆模型の実際の filtered 余極限。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
universe u
variable {k R C : Type u} [CommRing k] [CommRing R] [CommRing C]
  [Algebra k R] [Algebra k C] (g : R →ₐ[k] C)

/-- 全模型の実際の環写像の図式。 -/
def coefficientModelArrowDiagram : CoefficientModelCategory k g ⥤ Arrow CommRingCat.{u} :=
  CostructuredArrow.proj (coefficientVCoverModelFGInclusion k) (Arrow.mk (CommAlgCat.ofHom g)) ⋙
    coefficientVCoverModelFGInclusion k ⋙ (forget₂ (CommAlgCat k) CommRingCat).mapArrow

/-- 元の g と、各模型の実際の正方形からなる cocone。 -/
def coefficientModelArrowCocone : Cocone (coefficientModelArrowDiagram g) where
  pt := Arrow.mk (CommRingCat.ofHom g.toRingHom)
  ι.app X := (forget₂ (CommAlgCat k) CommRingCat).mapArrow.map X.hom
  ι.naturality {X Y} f := by
    change (forget₂ (CommAlgCat k) CommRingCat).mapArrow.map
      ((coefficientVCoverModelFGInclusion k).map f.left) ≫
        (forget₂ (CommAlgCat k) CommRingCat).mapArrow.map Y.hom =
      (forget₂ (CommAlgCat k) CommRingCat).mapArrow.map X.hom ≫ 𝟙 _
    rw [Category.comp_id, ← Functor.map_comp, f.w]

/-- 全模型の基底の環の図式。 -/
def coefficientModelBaseDiagram : CoefficientModelCategory k g ⥤ CommRingCat.{u} :=
  coefficientModelArrowDiagram g ⋙ Arrow.leftFunc

/-- 全模型の始域の環の図式。 -/
def coefficientModelSourceDiagram : CoefficientModelCategory k g ⥤ CommRingCat.{u} :=
  coefficientModelArrowDiagram g ⋙ Arrow.rightFunc

/-- 元の R への実際の cocone。 -/
def coefficientModelBaseCocone : Cocone (coefficientModelBaseDiagram g) :=
  Arrow.leftFunc.mapCocone (coefficientModelArrowCocone g)

/-- 元の C への実際の cocone。 -/
def coefficientModelSourceCocone : Cocone (coefficientModelSourceDiagram g) :=
  Arrow.rightFunc.mapCocone (coefficientModelArrowCocone g)

/-- 同じ宇宙の小さい全模型の環写像の図式。 -/
def coefficientModelSmallArrowDiagram : CoefficientModelIndex g ⥤ Arrow CommRingCat.{u} :=
  (equivSmallModel (CoefficientModelCategory k g)).inverse ⋙ coefficientModelArrowDiagram g

/-- 小さい全模型から元の g への cocone。 -/
def coefficientModelSmallArrowCocone : Cocone (coefficientModelSmallArrowDiagram g) :=
  (coefficientModelArrowCocone g).whisker (equivSmallModel (CoefficientModelCategory k g)).inverse

/-- 小さい全模型の基底の環の図式。 -/
def coefficientModelSmallBaseDiagram : CoefficientModelIndex g ⥤ CommRingCat.{u} :=
  coefficientModelSmallArrowDiagram g ⋙ Arrow.leftFunc

/-- 小さい全模型の始域の環の図式。 -/
def coefficientModelSmallSourceDiagram : CoefficientModelIndex g ⥤ CommRingCat.{u} :=
  coefficientModelSmallArrowDiagram g ⋙ Arrow.rightFunc

/-- 小さい全模型から元の R への cocone。 -/
def coefficientModelSmallBaseCocone : Cocone (coefficientModelSmallBaseDiagram g) :=
  Arrow.leftFunc.mapCocone (coefficientModelSmallArrowCocone g)

/-- 小さい全模型から元の C への cocone。 -/
def coefficientModelSmallSourceCocone : Cocone (coefficientModelSmallSourceDiagram g) :=
  Arrow.rightFunc.mapCocone (coefficientModelSmallArrowCocone g)

end SerrePositivity.AlgebraicGeometry
