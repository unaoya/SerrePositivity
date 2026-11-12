module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuAbsoluteTriangleFactor
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuZeroCornerComparison

/-!
概要：実 ν 面と同じ絶対面の元上三角形の二短辺を回収する。
方針：元正方形の二辺回収と標準三角形の面制限を照合する。
規約：元の二胞体と辺を選び直さない。使われ方：混合 Hom の共通境界。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial

private lemma nullUpperTriangleFace {X : SSet.{u}}
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) (k : Fin 3)
    (b : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1])
    (hb : stdSimplex.δ k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 = b) :
    X.δ k (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ F)) = SSet.yonedaEquiv (b ≫ F) := by
  rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, hb]

variable (R : Type u) [CommRing R] (d : DGOdotInput R)

/-- 概要：元実上三角形の最初の短辺は同じ固定 ν 実零角への辺。
方針：元正方形の左辺と元三角形の二番面を照合する。
規約：元一単体の等号。使われ方：混合面の実零角への境界。 -/
lemma dgOdotMilnorNuNullUpperTriangle_left :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}.δ (2 : Fin 3) (dgOdotMilnorNuNullTriangle R d 0) =
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorNuZeroActualLeft R d)).edge := by
  have hn : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorNuZeroActualLeft R d)).edge := by
    rw [← Category.assoc, (dgOdotMilnorPerfectNullSquare_edges R d).2.2.1]
    change SSet.yonedaEquiv.symm ((dgKInputNu R).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgFixedNullLeft R (A := dgOdotMilnorFlatKernelInput R d))).edge) = _
    exact congrArg SSet.yonedaEquiv.symm
      (dgKInputNu_edge R (dgFixedNullLeft R (A := dgOdotMilnorFlatKernelInput R d)))
  exact (nullUpperTriangleFace (dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R)
    2 _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableSquareTriangle_leftEdge).trans
      ((congrArg SSet.yonedaEquiv hn).trans (Equiv.apply_symm_apply _ _))

/-- 概要：元実上三角形の最後の短辺は同じ固定 ν 実上辺。
方針：元正方形の上辺と元三角形の零番面を照合する。
規約：元一単体の等号。使われ方：混合面の元上辺の境界。 -/
lemma dgOdotMilnorNuNullUpperTriangle_top :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}.δ (0 : Fin 3) (dgOdotMilnorNuNullTriangle R d 0) =
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorNuZeroActualTop R d)).edge := by
  have hn : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorNuZeroActualTop R d)).edge := by
    rw [← Category.assoc, (dgOdotMilnorPerfectNullSquare_edges R d).2.2.2]
    change SSet.yonedaEquiv.symm ((dgKInputNu R).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgFixedNullTop R (dgOdotMilnorFlatKernelContracted R d))).edge) = _
    exact congrArg SSet.yonedaEquiv.symm
      (dgKInputNu_edge R (dgFixedNullTop R (dgOdotMilnorFlatKernelContracted R d)))
  exact (nullUpperTriangleFace (dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R)
    0 _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTriangle_topEdge).trans
      ((congrArg SSet.yonedaEquiv hn).trans (Equiv.apply_symm_apply _ _))

variable (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：同じ絶対上三角形の最初の短辺は同じ標準零角への射。
方針：選択した元絶対四角形の左辺回収を使う。
規約：元一単体の等号。使われ方：混合面の絶対側の実零角への境界。 -/
lemma dgOdotMilnorNuAbsoluteUpperTriangle_left :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}.δ (2 : Fin 3) (dgOdotMilnorNuAbsoluteNullTriangle R d h 0) =
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (dgOdotMilnorNuPerfectSequence R d h).verdier.left)).edge :=
  (nullUpperTriangleFace (perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h))
    2 _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableSquareTriangle_leftEdge).trans
      ((congrArg SSet.yonedaEquiv
        (perfectVerdierRawSquare_edges (dgOdotMilnorNuPerfectSequence R d h)).2.2.1).trans
          (Equiv.apply_symm_apply _ _))

/-- 概要：同じ絶対上三角形の最後の短辺は同じ標準零角からの射。
方針：選択した元絶対四角形の上辺回収を使う。
規約：元一単体の等号。使われ方：混合面の絶対側の商境界。 -/
lemma dgOdotMilnorNuAbsoluteUpperTriangle_top :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}.δ (0 : Fin 3) (dgOdotMilnorNuAbsoluteNullTriangle R d h 0) =
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (fromZeroCategory (dgOdotMilnorNuPerfectSequence R d h).right)).edge :=
  (nullUpperTriangleFace (perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h))
    0 _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTriangle_topEdge).trans
      ((congrArg SSet.yonedaEquiv
        (perfectVerdierRawSquare_edges (dgOdotMilnorNuPerfectSequence R d h)).2.1).trans
          (Equiv.apply_symm_apply _ _))

end SerrePositivity.KST.SConstruction
