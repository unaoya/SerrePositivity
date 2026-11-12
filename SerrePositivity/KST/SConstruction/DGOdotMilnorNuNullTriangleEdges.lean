module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuAbsoluteTriangleFactor

/-!
概要：実 ν 面と同じ絶対面の元下三角形の二短辺を回収する。
方針：元正方形の二辺回収と標準三角形の面制限を照合する。
規約：元の二胞体と辺を選び直さない。使われ方：混合 Hom の共通境界。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial

private lemma nullLowerTriangleFace {X : SSet.{u}}
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) (k : Fin 3)
    (b : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1])
    (hb : stdSimplex.δ k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 = b) :
    X.δ k (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ F)) = SSet.yonedaEquiv (b ≫ F) := by
  rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, hb]

variable (R : Type u) [CommRing R] (d : DGOdotInput R)

/-- 概要：元実下三角形の最初の短辺は同じ固定 ν 包含辺。
方針：元正方形の下辺と元三角形の二番面を照合する。
規約：元一単体の等号。使われ方：混合面の包含境界。 -/
lemma dgOdotMilnorNuNullLowerTriangle_inclusion :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}.δ (2 : Fin 3) (dgOdotMilnorNuNullTriangle R d 1) =
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorFlatKernelExactMap R d)).edge := by
  have hn : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorFlatKernelExactMap R d)).edge := by
    rw [← Category.assoc, (dgOdotMilnorPerfectNullSquare_edges R d).1]
    change SSet.yonedaEquiv.symm ((dgKInputNu R).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorFlatKernelInputMap R d)).edge) = _
    exact congrArg SSet.yonedaEquiv.symm
      (dgKInputNu_edge R (dgOdotMilnorFlatKernelInputMap R d))
  exact (nullLowerTriangleFace (dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R)
    2 _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableSquareTriangle_bottomEdge).trans
      ((congrArg SSet.yonedaEquiv hn).trans (Equiv.apply_symm_apply _ _))

/-- 概要：元実下三角形の最後の短辺は同じ固定 ν 商辺。
方針：元正方形の右辺と元三角形の零番面を照合する。
規約：元一単体の等号。使われ方：混合面の指定商境界。 -/
lemma dgOdotMilnorNuNullLowerTriangle_projection :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}.δ (0 : Fin 3) (dgOdotMilnorNuNullTriangle R d 1) =
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorCellProjectionExactMap R d)).edge := by
  have hn : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorCellProjectionExactMap R d)).edge := by
    rw [← Category.assoc, (dgOdotMilnorPerfectNullSquare_edges R d).2.1]
    change SSet.yonedaEquiv.symm ((dgKInputNu R).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorCellProjectionInputMap R d)).edge) = _
    exact congrArg SSet.yonedaEquiv.symm
      (dgKInputNu_edge R (dgOdotMilnorCellProjectionInputMap R d))
  exact (nullLowerTriangleFace (dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R)
    0 _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTriangle_rightEdge).trans
      ((congrArg SSet.yonedaEquiv hn).trans (Equiv.apply_symm_apply _ _))

variable (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：同じ絶対下三角形の最初の短辺は同じ元包含。
方針：選択した元絶対四角形の下辺回収を使う。
規約：元一単体の等号。使われ方：混合面の絶対側の包含境界。 -/
lemma dgOdotMilnorNuAbsoluteLowerTriangle_inclusion :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}.δ (2 : Fin 3) (dgOdotMilnorNuAbsoluteNullTriangle R d h 1) =
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorNuPerfectSequence R d h).verdier.inclusion).edge :=
  (nullLowerTriangleFace (perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h))
    2 _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableSquareTriangle_bottomEdge).trans
      ((congrArg SSet.yonedaEquiv
        (perfectVerdierRawSquare_edges (dgOdotMilnorNuPerfectSequence R d h)).1).trans
          (Equiv.apply_symm_apply _ _))

/-- 概要：同じ絶対下三角形の最後の短辺は同じ元完備化後射影。
方針：選択した元絶対四角形の右辺回収を使う。
規約：元一単体の等号。使われ方：混合面の絶対側の商境界。 -/
lemma dgOdotMilnorNuAbsoluteLowerTriangle_projection :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}.δ (0 : Fin 3) (dgOdotMilnorNuAbsoluteNullTriangle R d h 1) =
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorNuPerfectSequence R d h).projection).edge :=
  (nullLowerTriangleFace (perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h))
    0 _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTriangle_rightEdge).trans
      ((congrArg SSet.yonedaEquiv
        (perfectVerdierRawSquare_edges (dgOdotMilnorNuPerfectSequence R d h)).2.2.2).trans
          (Equiv.apply_symm_apply _ _))

end SerrePositivity.KST.SConstruction
