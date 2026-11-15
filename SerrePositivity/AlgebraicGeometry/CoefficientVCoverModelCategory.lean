module

public import SerrePositivity.AlgebraicGeometry.SchemeVCover
public import Mathlib.Algebra.Category.CommAlgCat.FiniteType
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small

/-!
概要：有限型係数環上の affine v 被覆模型を、基底も保持する射の圏にまとめる。
方針：有限生成代数の Arrow から元の環写像への射の圏を、v 判定で制限する。
規約：実際の正方形と両辺の cocone を保つ。filtered 性は別に証明する。
使われ方：B03・B04 の被覆模型の整合する図式。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
universe u
variable (k : Type u) [CommRing k]

/-- 有限生成代数の射の圏も同じ宇宙で essentially small。 -/
instance coefficientVCoverFGArrow_essentiallySmall :
    EssentiallySmall.{u} (Arrow (FGAlgCat.{u} k)) :=
  EssentiallySmall.mk' (Functor.mapArrowEquivalence (equivSmallModel (FGAlgCat.{u} k)))

/-- 有限生成代数の射を、同じ係数環上の一般の代数の射へ送る。 -/
abbrev coefficientVCoverModelFGInclusion : Arrow (FGAlgCat.{u} k) ⥤ Arrow (CommAlgCat.{u} k) :=
  (ObjectProperty.ι (fun A : CommAlgCat.{u} k ↦ Algebra.FiniteType k A)).mapArrow

variable {R C : Type u} [CommRing R] [CommRing C] [Algebra k R] [Algebra k C]
variable (g : R →ₐ[k] C)

/-- 有限型な両辺を持つ模型の射が affine v 被覆であるという条件。 -/
def coefficientVCoverModelProperty : ObjectProperty
    (CostructuredArrow (coefficientVCoverModelFGInclusion k)
      (Arrow.mk (CommAlgCat.ofHom g))) :=
  fun X ↦ IsAffineVCover X.left.hom.hom.hom.toRingHom

/-- 元の環写像への可換な正方形を持つ、有限型 affine v 被覆の模型の圏。 -/
abbrev CoefficientVCoverModelCategory := (coefficientVCoverModelProperty k g).FullSubcategory

instance : EssentiallySmall.{u} (CoefficientVCoverModelCategory k g) :=
  essentiallySmall_of_fully_faithful (coefficientVCoverModelProperty k g).ι

/-- 模型の両辺と構造射を保持する、実際の環の Arrow の図式。 -/
def coefficientVCoverModelArrowDiagram : CoefficientVCoverModelCategory k g ⥤
    Arrow CommRingCat.{u} :=
  (coefficientVCoverModelProperty k g).ι ⋙
    CostructuredArrow.proj (coefficientVCoverModelFGInclusion k)
      (Arrow.mk (CommAlgCat.ofHom g)) ⋙ coefficientVCoverModelFGInclusion k ⋙
        (forget₂ (CommAlgCat k) CommRingCat).mapArrow

/-- 元の環写像へ向かう実際の可換な正方形の cocone。 -/
def coefficientVCoverModelArrowCocone : Cocone (coefficientVCoverModelArrowDiagram k g) where
  pt := Arrow.mk (CommRingCat.ofHom g.toRingHom)
  ι.app X := (forget₂ (CommAlgCat k) CommRingCat).mapArrow.map X.obj.hom
  ι.naturality {X Y} f := by
    change (forget₂ (CommAlgCat k) CommRingCat).mapArrow.map
        ((coefficientVCoverModelFGInclusion k).map f.hom.left) ≫
      (forget₂ (CommAlgCat k) CommRingCat).mapArrow.map Y.obj.hom =
      (forget₂ (CommAlgCat k) CommRingCat).mapArrow.map X.obj.hom ≫ 𝟙 _
    rw [Category.comp_id, ← Functor.map_comp, f.hom.w]

/-- 模型の基底側の実際の環の図式。 -/
def coefficientVCoverModelBaseDiagram : CoefficientVCoverModelCategory k g ⥤ CommRingCat.{u} :=
  coefficientVCoverModelArrowDiagram k g ⋙ Arrow.leftFunc

/-- 模型の始域側の実際の環の図式。 -/
def coefficientVCoverModelSourceDiagram : CoefficientVCoverModelCategory k g ⥤ CommRingCat.{u} :=
  coefficientVCoverModelArrowDiagram k g ⋙ Arrow.rightFunc

/-- 基底側の元の環 R への構造射からなる cocone。 -/
def coefficientVCoverModelBaseCocone : Cocone (coefficientVCoverModelBaseDiagram k g) :=
  Arrow.leftFunc.mapCocone (coefficientVCoverModelArrowCocone k g)

/-- 始域側の元の環 C への構造射からなる cocone。 -/
def coefficientVCoverModelSourceCocone : Cocone (coefficientVCoverModelSourceDiagram k g) :=
  Arrow.rightFunc.mapCocone (coefficientVCoverModelArrowCocone k g)

/-- 基底側から始域側への模型の射は自然変換。 -/
def coefficientVCoverModelMap : coefficientVCoverModelBaseDiagram k g ⟶
    coefficientVCoverModelSourceDiagram k g :=
  Functor.whiskerLeft (coefficientVCoverModelArrowDiagram k g) Arrow.leftToRight

/-- 同じ宇宙に取った被覆模型の添字。 -/
abbrev CoefficientVCoverModelIndex := SmallModel.{u} (CoefficientVCoverModelCategory k g)

/-- 小さい添字による、実際の環写像の図式。 -/
def coefficientVCoverModelSmallArrowDiagram : CoefficientVCoverModelIndex k g ⥤
    Arrow CommRingCat.{u} :=
  (equivSmallModel (CoefficientVCoverModelCategory k g)).inverse ⋙
    coefficientVCoverModelArrowDiagram k g

/-- 小さい添字の図式から元の環写像へ向かう cocone。 -/
def coefficientVCoverModelSmallArrowCocone :
    Cocone (coefficientVCoverModelSmallArrowDiagram k g) :=
  (coefficientVCoverModelArrowCocone k g).whisker
    (equivSmallModel (CoefficientVCoverModelCategory k g)).inverse

end SerrePositivity.AlgebraicGeometry
