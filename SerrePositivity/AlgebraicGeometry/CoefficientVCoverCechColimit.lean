module

public import SerrePositivity.AlgebraicGeometry.CoefficientVCoverModelFinal
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
概要：被覆模型の実際の余極限を、増大 Čech conerve 全体の自然な比較へ渡す。
方針：既存の conerve 関手の左随伴性による余極限保存を用いる。
規約：面・退化・増大写像を同じ余単体対象の同型で保つ。完全性の議論は再実装しない。
使われ方：B04 から B1 の filtered Čech 完全性への自然な入口。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
universe u
variable (k : Type u) [CommRing k] [IsNoetherianRing k]
  {R C : Type u} [CommRing R] [CommRing C] [Algebra k R] [Algebra k C] (g : R →ₐ[k] C)

/-- 小さい被覆模型の増大 Čech conerve の実際の図式。 -/
def coefficientVCoverModelCechDiagram : CoefficientVCoverModelIndex k g ⥤
    CosimplicialObject.Augmented CommRingCat.{u} :=
  coefficientVCoverModelSmallArrowDiagram k g ⋙ CosimplicialObject.augmentedCechConerve

/-- 元の g の conerve を頂点とする、模型の conerve の実際の cocone。 -/
def coefficientVCoverModelCechCocone : Cocone (coefficientVCoverModelCechDiagram k g) :=
  CosimplicialObject.augmentedCechConerve.mapCocone (coefficientVCoverModelSmallArrowCocone k g)

/-- 増大余単体環の圏の既存の comma-colimit を、この実際の図式に供給する。 -/
instance coefficientVCoverModelCechDiagram_hasColimit :
    HasColimit (coefficientVCoverModelCechDiagram k g) := by
  letI : HasColimitsOfSize.{u, u} (CosimplicialObject.Augmented CommRingCat.{u}) :=
    inferInstanceAs (HasColimitsOfSize.{u, u}
      (Comma (CosimplicialObject.const CommRingCat.{u})
        (𝟭 (CosimplicialObject CommRingCat.{u}))))
  infer_instance

variable (hv : IsAffineVCover g.toRingHom)
include hv

/-- 模型の conerve の実際の cocone は増大余単体環の圏で colimit。 -/
def coefficientVCoverModelCechCoconeIsColimit : IsColimit (coefficientVCoverModelCechCocone k g) := by
  let G : Arrow CommRingCat.{u} ⥤ CosimplicialObject.Augmented CommRingCat.{u} :=
    CosimplicialObject.augmentedCechConerve
  letI : G.IsLeftAdjoint := CosimplicialObject.cechConerveAdjunction.isLeftAdjoint
  exact isColimitOfPreserves G (coefficientVCoverModelSmallArrowCoconeIsColimit k g hv)

/-- 面・退化・増大写像を保つ、実際の模型の conerve と元の conerve の比較。 -/
def coefficientVCoverModelCechComparison : colimit (coefficientVCoverModelCechDiagram k g) ≅
    CosimplicialObject.augmentedCechConerve.obj (Arrow.mk (CommRingCat.ofHom g.toRingHom)) :=
  (colimit.isColimit _).coconePointUniqueUpToIso (coefficientVCoverModelCechCoconeIsColimit k g hv)

end SerrePositivity.AlgebraicGeometry
