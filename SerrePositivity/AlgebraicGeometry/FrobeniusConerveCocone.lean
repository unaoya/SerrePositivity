module

public import SerrePositivity.AlgebraicGeometry.FrobeniusArrowCocone
public import SerrePositivity.AlgebraicGeometry.FrobeniusConerveStep
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
概要：実際の Frobenius の矢印の余錐を、同じ conerve の各次数へ渡す。
方針：既存の増大 conerve の随伴と、忘却・評価の余極限保存を使う。
規約：点は実際の frobeniusDirectLimitMap の conerve の環、脚も元の有限段の射。
使われ方：同じ conerve の係数環の順極限との標準比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable (f : Arrow CommRingCat.{u}) (p : ℕ) (hp : p.Prime)
variable (hA : (p : f.left) = 0) (hB : (p : f.right) = 0)

/-- 実際の矢印の標準余錐を、既存の同じ conerve の各次数で写した余錐。 -/
def frobeniusConerveCocone (n : SimplexCategory) :
    Cocone (frobeniusArrowDiagram f p hp hA hB ⋙ CosimplicialObject.cechConerve ⋙
      (evaluation SimplexCategory CommRingCat.{u}).obj n) :=
  (CosimplicialObject.cechConerve ⋙ (evaluation SimplexCategory CommRingCat.{u}).obj n).mapCocone
    (frobeniusArrowCocone f p hp hA hB)

/-- 同じ余錐の普遍性は、既存の増大 conerve・忘却・評価の余極限保存から得られる。 -/
def frobeniusConerveIsColimit (n : SimplexCategory) :
    IsColimit (frobeniusConerveCocone f p hp hA hB n) := by
  let G : Arrow CommRingCat.{u} ⥤ CosimplicialObject.Augmented CommRingCat.{u} :=
    CosimplicialObject.augmentedCechConerve
  letI : G.IsLeftAdjoint := CosimplicialObject.cechConerveAdjunction.isLeftAdjoint
  haveI : PreservesColimitsOfShape ℕ
      (CosimplicialObject.Augmented.drop : CosimplicialObject.Augmented CommRingCat.{u} ⥤ _) := by
    change PreservesColimitsOfShape ℕ (Comma.snd _ _)
    infer_instance
  change IsColimit ((G ⋙ CosimplicialObject.Augmented.drop ⋙
    (evaluation SimplexCategory CommRingCat.{u}).obj n).mapCocone
      (frobeniusArrowCocone f p hp hA hB))
  exact isColimitOfPreserves _ (frobeniusArrowIsColimit f p hp hA hB)

end SerrePositivity.AlgebraicGeometry
