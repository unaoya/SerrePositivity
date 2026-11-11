module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullTrianglePrismVertexPaths

/-!
概要：元上下二胞体の各全比較から、元共有対角の端点固定ホモトピーを取り出す。
方針：同じ実対角辺への制限と元三頂点経路の厳密回収を使う。
規約：二つの対角ホモトピーの一致は主張しない。元両対角辺と二端点は固定する。
使われ方：依頼済みの全境界充填に渡す実共有対角比較の候補。
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
local notation "B" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)

/-- 概要：元下二胞体の同じ全比較の元共有対角への実制限。
方針：元対角面の厳密回収で同じ比較を制限する。
規約：元実／絶対対角辺を保持。使われ方：元全比較の共有対角側面。 -/
def dgOdotMilnorNuNullLowerDiagonalHomotopy : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareDiagonal ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareDiagonal ≫ perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h)) where
  h := (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 2})) ≫
    (dgOdotMilnorNuNullLowerTriangleHomotopy R d h).h
  h₀ := by
    rw [ι₀_comp_assoc, SSet.Homotopy.h₀]
    exact dgOdotMilnorNuNullPrismTriangle_diagonal_actual R d 1
  h₁ := by
    rw [ι₁_comp_assoc, SSet.Homotopy.h₁]
    exact dgOdotMilnorNuNullPrismTriangle_diagonal_absolute R d h 1
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：元下全比較から取った対角側面の二端点は元恒等経路。
方針：同じ元三頂点の始点・終点経路を対角面へ回収する。
規約：全一単体の厳密等号。使われ方：二対角候補の同じ端点固定条件。 -/
lemma dgOdotMilnorNuNullLowerDiagonalHomotopy_paths :
    (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuNullLowerDiagonalHomotopy R d h).h =
      snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (𝟙 (K : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}))).edge ∧
      (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuNullLowerDiagonalHomotopy R d h).h =
      snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (𝟙 (B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}))).edge := by
  have hs : (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u + 2}) ⟶ Δ[1]) ≫
      stdSimplex.δ (1 : Fin 3) = stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) := by
    apply SSet.yonedaEquiv.injective
    decide
  have ht : (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u + 2}) ⟶ Δ[1]) ≫
      stdSimplex.δ (1 : Fin 3) = stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) := by
    apply SSet.yonedaEquiv.injective
    decide
  constructor
  · change (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫
      (stdSimplex.δ (1 : Fin 3) ▷ Δ[1]) ≫
        (dgOdotMilnorNuNullLowerTriangleHomotopy R d h).h = _
    rw [← Category.assoc, ← comp_whiskerRight, hs]
    exact (dgOdotMilnorNuNullLowerTriangleHomotopy_paths R d h).1
  · change (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫
      (stdSimplex.δ (1 : Fin 3) ▷ Δ[1]) ≫
        (dgOdotMilnorNuNullLowerTriangleHomotopy R d h).h = _
    rw [← Category.assoc, ← comp_whiskerRight, ht]
    exact (dgOdotMilnorNuNullLowerTriangleHomotopy_paths R d h).2.2

/-- 概要：元上二胞体の同じ全比較の元共有対角への実制限。
方針：元対角面の厳密回収で同じ比較を制限する。
規約：元実／絶対対角辺を保持。使われ方：元全比較の共有対角側面。 -/
def dgOdotMilnorNuNullUpperDiagonalHomotopy : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareDiagonal ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareDiagonal ≫ perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h)) where
  h := (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 2})) ≫
    (dgOdotMilnorNuNullUpperTriangleHomotopy R d h).h
  h₀ := by
    rw [ι₀_comp_assoc, SSet.Homotopy.h₀]
    exact dgOdotMilnorNuNullPrismTriangle_diagonal_actual R d 0
  h₁ := by
    rw [ι₁_comp_assoc, SSet.Homotopy.h₁]
    exact dgOdotMilnorNuNullPrismTriangle_diagonal_absolute R d h 0
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：元上全比較から取った対角側面の二端点は元恒等経路。
方針：同じ元三頂点の始点・終点経路を対角面へ回収する。
規約：全一単体の厳密等号。使われ方：二対角候補の同じ端点固定条件。 -/
lemma dgOdotMilnorNuNullUpperDiagonalHomotopy_paths :
    (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuNullUpperDiagonalHomotopy R d h).h =
      snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (𝟙 (K : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}))).edge ∧
      (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuNullUpperDiagonalHomotopy R d h).h =
      snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (𝟙 (B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}))).edge := by
  have hs : (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u + 2}) ⟶ Δ[1]) ≫
      stdSimplex.δ (1 : Fin 3) = stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) := by
    apply SSet.yonedaEquiv.injective
    decide
  have ht : (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u + 2}) ⟶ Δ[1]) ≫
      stdSimplex.δ (1 : Fin 3) = stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) := by
    apply SSet.yonedaEquiv.injective
    decide
  constructor
  · change (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫
      (stdSimplex.δ (1 : Fin 3) ▷ Δ[1]) ≫
        (dgOdotMilnorNuNullUpperTriangleHomotopy R d h).h = _
    rw [← Category.assoc, ← comp_whiskerRight, hs]
    exact (dgOdotMilnorNuNullUpperTriangleHomotopy_paths R d h).1
  · change (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫
      (stdSimplex.δ (1 : Fin 3) ▷ Δ[1]) ≫
        (dgOdotMilnorNuNullUpperTriangleHomotopy R d h).h = _
    rw [← Category.assoc, ← comp_whiskerRight, ht]
    exact (dgOdotMilnorNuNullUpperTriangleHomotopy_paths R d h).2.2

end SerrePositivity.KST.SConstruction
