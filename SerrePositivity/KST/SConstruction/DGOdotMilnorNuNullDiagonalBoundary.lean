module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullDiagonalComparison

/-!
概要：元実／絶対四角形の元共有対角全辺を同じ指定比較で結ぶ。
方針：元対角完全射の一単体回収を標準共有面へ戻し、完備包含で反映する。
規約：元全辺・同じ比較辺を保持。使われ方：元上下二胞体を貼る共通境界。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial

private lemma zeroSquareDiagonalSimplex {X : SSet.{u}}
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) :
    X.δ (1 : Fin 3) (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ F)) =
      SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareDiagonal ≫ F) := by
  rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle_diagonal]

variable (R : Type u) [CommRing R] (d : DGOdotInput R)

/-- 概要：元実共有対角の完全射の全辺は同じ元実四角形の対角。
方針：元共有面と元完全射の一単体回収を使う。
規約：元全一単体の等号。使われ方：元実共有辺への厳密復元。 -/
lemma dgOdotMilnorNuNullDiagonalMap_diagram :
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorNuNullDiagonalMap R d)).edge =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareDiagonal ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R := by
  apply SSet.yonedaEquiv.injective
  exact (Equiv.apply_symm_apply _ _).trans
    ((dgOdotMilnorNuNullDiagonalMap_edge R d 0).trans
      (zeroSquareDiagonalSimplex (dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R)))

variable (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：元絶対共有対角の完全射の全辺は同じ元絶対四角形の対角。
方針：同じ元共有面と元一単体回収を使う。
規約：元全一単体の等号。使われ方：元絶対共有辺への厳密復元。 -/
lemma dgOdotMilnorNuAbsoluteDiagonalMap_diagram :
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorNuAbsoluteDiagonalMap R d h)).edge =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareDiagonal ≫ perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h) := by
  apply SSet.yonedaEquiv.injective
  exact (Equiv.apply_symm_apply _ _).trans
    ((dgOdotMilnorNuAbsoluteDiagonalMap_edge R d h 0).trans
      (zeroSquareDiagonalSimplex (perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h))))

/-- 概要：元実／絶対四角形の共有対角全辺を同じ指定比較で結ぶ。
方針：同じ固定端点の全一単体比較を元二対角へ等号で戻す。
規約：元の比較辺を保持。使われ方：上下二胞体比較の共通 StableInfinity 境界。 -/
def dgOdotMilnorNuNullDiagonalDiagramComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareDiagonal ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareDiagonal ≫ perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h)) :=
  Eq.mp (congrArg₂ (fun f g : (Δ[1] : SSet.{u + 2}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g)
    (dgOdotMilnorNuNullDiagonalMap_diagram R d) (dgOdotMilnorNuAbsoluteDiagonalMap_diagram R d h))
      (dgOdotMilnorNuNullDiagonalArrowComparison R d h)

/-- 概要：元実／絶対 Cat^perf 四角形の元共有対角を同じ全辺比較で結ぶ。
方針：同じ完備包含で元 StableInfinity 比較を反映する。
規約：元の両図式・同じ共有対角。使われ方：Sp の全図式比較を貼る共通境界。 -/
def dgOdotMilnorNuNullPerfectDiagonalDiagramComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareDiagonal ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareDiagonal ≫ (dgOdotMilnorNuPerfectSequence R d h).presentation.square) := by
  apply perfectStableInfinityInclusion_isFullyFaithful.preimageFunctorIso
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareDiagonal ≫ dgOdotMilnorPerfectNullSquare R d ≫
      dgKInputPerfectNu R ≫ perfectStableInfinityInclusion)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareDiagonal ≫ perfectVerdierSquare (dgOdotMilnorNuPerfectSequence R d h) ≫
      perfectStableInfinityInclusion)
  rw [dgKInputPerfectNu_inclusion, perfectVerdierSquare_inclusion]
  exact dgOdotMilnorNuNullDiagonalDiagramComparison R d h

end SerrePositivity.KST.SConstruction
