module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullLowerTriangleComparison
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullPrismFullBoundaryFaces

/-!
概要：元両端固定下比較 prism の指定包含・商側面を全単体で厳密回収する。
方針：元内ホーンの二面を同じ元境界入射に照合して制限式を合成する。
規約：元二短辺比較を保持。共有対角側面の指定は別工程。
使われ方：元下二胞体全比較の指定二短辺境界。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：元下比較 prism の元二短辺側面は同じ指定実ホモトピーそのもの。
方針：元内ホーンの二面を元全側境界の同じ面へ戻す。
規約：全正方形の等号。使われ方：元包含・元商比較の厳密保持。 -/
lemma dgOdotMilnorNuNullLowerPrism_face (i : Fin 3) (hi : i ≠ 1) :
    ((Δ[1] : SSet.{u + 2}) ◁ stdSimplex.δ i) ≫ dgOdotMilnorNuNullLowerPrism R d h =
      (β_ (Δ[1] : SSet.{u + 2}) Δ[1]).hom ≫
        dgOdotMilnorNuNullPrismSideFamily R d h 1 i := by
  have hface : horn.ι (1 : Fin 3) i hi ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornBoundaryInclusion 1 1 =
      (boundary.ι i : (Δ[1] : SSet.{u + 2}) ⟶ boundary 2) := by
    apply (cancel_mono (boundary 2).ι).mp
    have hι : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornBoundaryInclusion 1 1 ≫ (boundary 2 : (Δ[2] : SSet.{u + 2}).Subcomplex).ι =
        (horn 2 1).ι := rfl
    rw [Category.assoc, hι, horn.ι_ι, boundary.ι_ι]
  rw [← horn.ι_ι (1 : Fin 3) i hi, whiskerLeft_comp, Category.assoc,
    (dgOdotMilnorNuNullLowerPrism_restrictions R d h).1,
    ← Category.assoc, ← whiskerLeft_comp, hface]
  exact dgOdotMilnorNuNullPrismTimeBoundary_face R d h 1 i

/-- 概要：元下二胞体の全比較ホモトピーも元包含・商側面の同じ全射を保つ。
方針：元 prism の短辺制限を因子交換の自然性で元向きへ戻す。
規約：全単体の等号。使われ方：元全比較の指定短辺の回収。 -/
lemma dgOdotMilnorNuNullLowerTriangleHomotopy_face (i : Fin 3) (hi : i ≠ 1) :
    (stdSimplex.δ i ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuNullLowerTriangleHomotopy R d h).h =
      dgOdotMilnorNuNullPrismSideFamily R d h 1 i := by
  have hs : (stdSimplex.δ i ▷ (Δ[1] : SSet.{u + 2})) ≫ (β_ Δ[2] Δ[1]).hom =
      (β_ (Δ[1] : SSet.{u + 2}) Δ[1]).hom ≫ (Δ[1] ◁ stdSimplex.δ i) := rfl
  change (stdSimplex.δ i ▷ (Δ[1] : SSet.{u + 2})) ≫ (β_ Δ[2] Δ[1]).hom ≫
    dgOdotMilnorNuNullLowerPrism R d h = _
  rw [← Category.assoc, hs, Category.assoc, dgOdotMilnorNuNullLowerPrism_face R d h i hi]
  let cancel (H : (Δ[1] ⊗ Δ[1] : SSet.{u + 2}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}) :
      (β_ (Δ[1] : SSet.{u + 2}) Δ[1]).hom ≫
        (β_ (Δ[1] : SSet.{u + 2}) Δ[1]).hom ≫ H = H := rfl
  exact cancel _

end SerrePositivity.KST.SConstruction
