module

public import SerrePositivity.KST.Spectra.SquareReducedDesc

/-!
概要：二つの円の reduced map を正方形へ引き戻すと四辺で定数となる。
方針：円の商射の境界条件と二つの軸の定数性を合成する。
規約：単体集合の射の厳密な等式を使う。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。smash 積から相対三角形への制限。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Y : PointedSimplicialSet.{u}}
  (f : PointedObject.ReducedPairMap PointedSimplicialSet.circle.{u}
    PointedSimplicialSet.circle.{u} Y)

/-- 概要：reduced map の正方形への引き戻しは縦辺で定数。
方針：第一の商射の境界条件を使い、残る商射を基点と交換する。
規約：二つの円への商射の積を前合成する。
使われ方：Goerss–Jardine I §7。相対三角形への制限の第一の境界条件。 -/
theorem reducedSquare_boundary_left :
    (boundary.{u} 1).ι ▷ (Δ[1] : SSet.{u}) ≫
      (PointedObject.cofiberQuotient (boundary.{u} 1).ι ⊗ₘ
        PointedObject.cofiberQuotient (boundary.{u} 1).ι) ≫ f.1 =
      toUnit ((boundary.{u} 1 : SSet.{u}) ⊗ (Δ[1] : SSet.{u})) ≫ Y.hom := by
  erw [tensorHom_def, ← Category.assoc, ← comp_whiskerRight_assoc,
    PointedObject.cofiberQuotient_condition, comp_whiskerRight_assoc,
    Category.assoc, Category.assoc, ← whisker_exchange_assoc, f.2.1]
  erw [comp_toUnit_assoc, comp_toUnit_assoc]

/-- 概要：reduced map の正方形への引き戻しは横辺で定数。
方針：第二の商射の境界条件を使い、第一の商射を基点と交換する。
規約：基点は標的の指定基点。
使われ方：Goerss–Jardine I §7。相対三角形への制限の第二の境界条件。 -/
theorem reducedSquare_boundary_right :
    (Δ[1] : SSet.{u}) ◁ (boundary.{u} 1).ι ≫
      (PointedObject.cofiberQuotient (boundary.{u} 1).ι ⊗ₘ
        PointedObject.cofiberQuotient (boundary.{u} 1).ι) ≫ f.1 =
      toUnit ((Δ[1] : SSet.{u}) ⊗ (boundary.{u} 1 : SSet.{u})) ≫ Y.hom := by
  erw [tensorHom_def', ← Category.assoc, ← whiskerLeft_comp_assoc,
    PointedObject.cofiberQuotient_condition, whiskerLeft_comp_assoc,
    Category.assoc, Category.assoc, whisker_exchange_assoc, f.2.2]
  erw [comp_toUnit_assoc, comp_toUnit_assoc]

end

end SerrePositivity.KST.Spectra
