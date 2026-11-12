module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorSourceSquare
public import SerrePositivity.KST.SConstruction.DGOdotMilnorPerfectNullSquare
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.SquarePastingRectangle
public import SerrePositivity.KST.SConstruction.DGKFixedInterface

/-!
概要：元始域の cell 分解から核への比較と同じ零化面を、実 S 長方形として貼る。
方針：核の全対象商の同じ ε を指定し、二面と上下の合成三角形を保持する。
規約：この始域比較長方形を LT の普遍差長方形と同一視しない。
使われ方：増大屋根を持つ二つの実零化面と、その指定全境界比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)

/-- 概要：同じ厳密核比較を全対象商へ写し、像の同じ ε を指定する。
方針：元の全対象商の指定収縮を使用する。規約：自然な収縮を仮定しない。
使われ方：元始域の全対象商からの実延長。 -/
def dgOdotMilnorSourceKernelNullContracted : DGQuotient.ContractedFunctor R
    (dgOdotMilnorSourceCellInput R d) Set.univ
    (dgFixedNullInput R (dgOdotMilnorFlatKernelInput R d)) where
  toDGFunctor := (dgOdotMilnorSourceKernelInputMap R d).down.comp
    (dgFixedNullLeft R (A := dgOdotMilnorFlatKernelInput R d)).down
  homotopy x := DGQuotient.epsilonElement R (dgOdotMilnorFlatKernelInput R d) Set.univ
    ⟨(dgOdotMilnorSourceKernelInputMap R d).down.obj x.val, Set.mem_univ _⟩
  d_homotopy x := DGQuotient.differential_epsilonElement R
    (dgOdotMilnorFlatKernelInput R d) Set.univ
      ⟨(dgOdotMilnorSourceKernelInputMap R d).down.obj x.val, Set.mem_univ _⟩

/-- 概要：同じ核比較と両全対象商包含を保つ実 S 零化面。
方針：Sp 正本の指定収縮からの実四角形を使用する。
規約：四辺の全一単体を保持する。使われ方：始域比較長方形の左面。 -/
def dgOdotMilnorSourceKernelNullSquare :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 2}) ⟶ dgKInputInfinity.{u, u + 1} R :=
  (exists_dgFixedNullSquare R (dgOdotMilnorSourceKernelInputMap R d)
    (dgFixedNullLeft R (A := dgOdotMilnorFlatKernelInput R d))
    (dgOdotMilnorSourceKernelNullContracted R d) rfl).choose

/-- 概要：同じ左面の四辺は元の核比較・商包含・商延長そのもの。
方針：同じ選択された実四角形の境界を回収する。
規約：別の辺の代表を選択しない。使われ方：核の実零化面との貼合せ。 -/
lemma dgOdotMilnorSourceKernelNullSquare_edges :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ dgOdotMilnorSourceKernelNullSquare R d =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorSourceKernelInputMap R d)).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgOdotMilnorSourceKernelNullSquare R d = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgFixedNullLeft R (A := dgOdotMilnorFlatKernelInput R d))).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgOdotMilnorSourceKernelNullSquare R d = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgFixedNullLeft R (A := dgOdotMilnorSourceCellInput R d))).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ dgOdotMilnorSourceKernelNullSquare R d = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
          (dgFixedNullTop R (dgOdotMilnorSourceKernelNullContracted R d))).edge :=
  (exists_dgFixedNullSquare R (dgOdotMilnorSourceKernelInputMap R d)
    (dgFixedNullLeft R (A := dgOdotMilnorFlatKernelInput R d))
    (dgOdotMilnorSourceKernelNullContracted R d) rfl).choose_spec

/-- 概要：同じ厳密核比較と核包含の実合成三角形。
方針：固定 S の元の合成を coherent nerve に写す。規約：全二単体を保持する。
使われ方：始域比較長方形の下境界。 -/
def dgOdotMilnorSourceNullBottomTriangle : SSet.Edge.CompStruct
    (X := dgKInputInfinity.{u, u + 1} R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorSourceKernelInputMap R d))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorFlatKernelInputMap R d))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorSourceKernelInputMap R d ≫
      dgOdotMilnorFlatKernelInputMap R d)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (dgOdotMilnorSourceKernelInputMap R d)
    (dgOdotMilnorFlatKernelInputMap R d)

/-- 概要：同じ二つの実全対象商延長の合成三角形。
方針：元の strict 合成を使用する。規約：上合成の二単体を選び直さない。
使われ方：始域比較長方形の上境界。 -/
def dgOdotMilnorSourceNullTopTriangle : SSet.Edge.CompStruct
    (X := dgKInputInfinity.{u, u + 1} R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgFixedNullTop R (dgOdotMilnorSourceKernelNullContracted R d)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgFixedNullTop R (dgOdotMilnorFlatKernelContracted R d)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgFixedNullTop R (dgOdotMilnorSourceKernelNullContracted R d) ≫
      dgFixedNullTop R (dgOdotMilnorFlatKernelContracted R d))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (dgFixedNullTop R (dgOdotMilnorSourceKernelNullContracted R d))
    (dgFixedNullTop R (dgOdotMilnorFlatKernelContracted R d))

/-- 概要：元始域の cell 分解・同じ核・同じ resolved 商の実 S 長方形。
方針：既構成の二つの零化面を同じ二つの合成三角形を保って貼る。
規約：元対角始域との回収は構成済み増大屋根を併用する。
使われ方：d④ の始域側の実全図式と指定境界。 -/
def dgOdotMilnorSourceNullRectangle : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.SquarePastingRectangle
    (dgOdotMilnorSourceKernelNullSquare R d) (dgOdotMilnorPerfectNullSquare R d)
    (SSet.yonedaEquiv.symm (dgOdotMilnorSourceNullBottomTriangle R d).simplex)
    (SSet.yonedaEquiv.symm (dgOdotMilnorSourceNullTopTriangle R d).simplex) := by
  have hL := dgOdotMilnorSourceKernelNullSquare_edges R d
  have hR := dgOdotMilnorPerfectNullSquare_edges R d
  apply Classical.choice
  apply _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.nonempty_squarePastingRectangle
  · exact hL.2.1.trans hR.2.2.1.symm
  · rw [hL.1, stdSimplex.δ_comp_yonedaEquiv_symm,
      (dgOdotMilnorSourceNullBottomTriangle R d).d₂]
    rfl
  · rw [hR.1, stdSimplex.δ_comp_yonedaEquiv_symm,
      (dgOdotMilnorSourceNullBottomTriangle R d).d₀]
    rfl
  · rw [hL.2.2.2, stdSimplex.δ_comp_yonedaEquiv_symm,
      (dgOdotMilnorSourceNullTopTriangle R d).d₂]
    rfl
  · rw [hR.2.2.2, stdSimplex.δ_comp_yonedaEquiv_symm,
      (dgOdotMilnorSourceNullTopTriangle R d).d₀]
    rfl

end SerrePositivity.KST.SConstruction
