module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullLowerPrismSides
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullUpperPrismSides

/-!
概要：元上下二胞体の全比較が保持する元三頂点の全経路を厳密に回収する。
方針：元二短辺側面の全回収と同じ元端点経路を合成する。
規約：下三頂点は元恒等、上の零角成分は同じ指定完全射。
使われ方：上下共有対角の端点固定比較を取り出す。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)
local notation "K" => dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d)
local notation "A" => dgKInputStableValue R (dgOdotMilnorCellInput R d)
local notation "B" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)
local notation "Z" => dgKInputStableValue R
  (dgFixedNullInput R (dgOdotMilnorFlatKernelInput R d))

/-- 概要：元下二胞体の全比較は元三頂点の同じ指定全経路を保持する。
方針：元二短辺側面と元の両端点経路を厳密回収する。
規約：元経路を選び直さない。使われ方：共有対角比較の同じ二端点の固定。 -/
lemma dgOdotMilnorNuNullLowerTriangleHomotopy_paths :
    ((stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3)) ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuNullLowerTriangleHomotopy R d h).h =
      snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (𝟙 (K : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}))).edge ∧
      ((stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3)) ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuNullLowerTriangleHomotopy R d h).h =
      snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (𝟙 (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}))).edge ∧
      ((stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3)) ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuNullLowerTriangleHomotopy R d h).h =
      snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (𝟙 (B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}))).edge := by
  constructor
  · rw [comp_whiskerRight, Category.assoc,
      dgOdotMilnorNuNullLowerTriangleHomotopy_face R d h 2 (by decide)]
    exact (dgOdotMilnorNuInclusionDiagramHomotopy_paths R d h).1
  · constructor
    · rw [comp_whiskerRight, Category.assoc,
        dgOdotMilnorNuNullLowerTriangleHomotopy_face R d h 2 (by decide)]
      exact (dgOdotMilnorNuInclusionDiagramHomotopy_paths R d h).2
    · rw [comp_whiskerRight, Category.assoc,
        dgOdotMilnorNuNullLowerTriangleHomotopy_face R d h 0 (by decide)]
      exact (dgOdotMilnorNuProjectionDiagramHomotopy_paths R d h).2

/-- 概要：元上二胞体の全比較は元三頂点の同じ指定全経路を保持する。
方針：元二短辺側面と元の両端点経路を厳密回収する。
規約：元経路を選び直さない。使われ方：共有対角比較の同じ二端点の固定。 -/
lemma dgOdotMilnorNuNullUpperTriangleHomotopy_paths :
    ((stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3)) ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuNullUpperTriangleHomotopy R d h).h =
      snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (𝟙 (K : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}))).edge ∧
      ((stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3)) ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuNullUpperTriangleHomotopy R d h).h =
      snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (Z))).edge ∧
      ((stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3)) ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuNullUpperTriangleHomotopy R d h).h =
      snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (𝟙 (B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}))).edge := by
  constructor
  · rw [comp_whiskerRight, Category.assoc,
      dgOdotMilnorNuNullUpperTriangleHomotopy_face R d h 2 (by decide)]
    exact (dgOdotMilnorNuZeroLeftDiagramHomotopy_paths R d h).1
  · constructor
    · rw [comp_whiskerRight, Category.assoc,
        dgOdotMilnorNuNullUpperTriangleHomotopy_face R d h 2 (by decide)]
      exact (dgOdotMilnorNuZeroLeftDiagramHomotopy_paths R d h).2
    · rw [comp_whiskerRight, Category.assoc,
        dgOdotMilnorNuNullUpperTriangleHomotopy_face R d h 0 (by decide)]
      exact (dgOdotMilnorNuZeroTopDiagramHomotopy_paths R d h).2

end SerrePositivity.KST.SConstruction
