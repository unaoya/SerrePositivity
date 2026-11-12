module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuInclusionDiagramHomotopy
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuProjectionDiagramHomotopy
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuZeroLeftDiagramHomotopy
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuZeroTopDiagramHomotopy
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullDiagonalDiagramHomotopy

/-!
概要：元上下二胞体の三つの比較側面を、同じ端点経路で厳密に揃える。
方針：元の包含・商・零角二辺と同じ共有対角ホモトピーを同時に使う。
規約：元実／絶対面を保持し、内部の三単体の充填は主張しない。
使われ方：全四面回収へ渡す元比較 prism の貼り合わせ可能な側境界。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：元上下二胞体の最初の短辺を結ぶ同じ実ホモトピー。
方針：上は元零角左辺、下は元核包含の指定ホモトピーを使う。
規約：元実辺と元絶対辺。使われ方：元比較 prism の最初の側面。 -/
def dgOdotMilnorNuNullPrismFirstHomotopy (j : Fin 2) : SSet.Homotopy
    (![_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge] j ≫
      dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R)
    (![_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge] j ≫
      perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h)) :=
  Fin.cases (dgOdotMilnorNuZeroLeftDiagramHomotopy R d h)
    (fun k : Fin 1 => Fin.cases (dgOdotMilnorNuInclusionDiagramHomotopy R d h)
      (fun e : Fin 0 => Fin.elim0 e) k) j

/-- 概要：元上下二胞体の最後の短辺を結ぶ同じ実ホモトピー。
方針：上は元零角上辺、下は元商の指定ホモトピーを使う。
規約：元実辺と元絶対辺。使われ方：元比較 prism の最後の側面。 -/
def dgOdotMilnorNuNullPrismLastHomotopy (j : Fin 2) : SSet.Homotopy
    (![_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge] j ≫
      dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R)
    (![_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge] j ≫
      perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h)) :=
  Fin.cases (dgOdotMilnorNuZeroTopDiagramHomotopy R d h)
    (fun k : Fin 1 => Fin.cases (dgOdotMilnorNuProjectionDiagramHomotopy R d h)
      (fun e : Fin 0 => Fin.elim0 e) k) j

/-- 概要：最初の側面と共有対角側面は元核上の同じ全端点経路で貼れる。
方針：両方の指定始点経路を同じ元恒等辺へ戻す。
規約：全一単体の厳密等号。使われ方：元始点の三面貼り合わせ。 -/
lemma dgOdotMilnorNuNullPrismSide_source (j : Fin 2) :
    (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuNullPrismFirstHomotopy R d h j).h =
      (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuNullDiagonalDiagramHomotopy R d h).h := by
  fin_cases j
  · exact (dgOdotMilnorNuZeroLeftDiagramHomotopy_paths R d h).1.trans
      (dgOdotMilnorNuNullDiagonalDiagramHomotopy_paths R d h).1.symm
  · exact (dgOdotMilnorNuInclusionDiagramHomotopy_paths R d h).1.trans
      (dgOdotMilnorNuNullDiagonalDiagramHomotopy_paths R d h).1.symm

/-- 概要：二つの短辺側面は同じ中間対象上の全端点経路で貼れる。
方針：上は同じ実零角成分、下は同じ元中間圏の恒等辺へ戻す。
規約：全一単体の厳密等号。使われ方：元中間頂点の二面貼り合わせ。 -/
lemma dgOdotMilnorNuNullPrismSide_middle (j : Fin 2) :
    (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuNullPrismFirstHomotopy R d h j).h =
      (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuNullPrismLastHomotopy R d h j).h := by
  fin_cases j
  · exact (dgOdotMilnorNuZeroLeftDiagramHomotopy_paths R d h).2.trans
      (dgOdotMilnorNuZeroTopDiagramHomotopy_paths R d h).1.symm
  · exact (dgOdotMilnorNuInclusionDiagramHomotopy_paths R d h).2.trans
      (dgOdotMilnorNuProjectionDiagramHomotopy_paths R d h).1.symm

/-- 概要：最後の側面と共有対角側面は元商上の同じ全端点経路で貼れる。
方針：両方の指定終点経路を同じ元恒等辺へ戻す。
規約：全一単体の厳密等号。使われ方：元終点の三面貼り合わせ。 -/
lemma dgOdotMilnorNuNullPrismSide_target (j : Fin 2) :
    (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuNullPrismLastHomotopy R d h j).h =
      (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuNullDiagonalDiagramHomotopy R d h).h := by
  fin_cases j
  · exact (dgOdotMilnorNuZeroTopDiagramHomotopy_paths R d h).2.trans
      (dgOdotMilnorNuNullDiagonalDiagramHomotopy_paths R d h).2.symm
  · exact (dgOdotMilnorNuProjectionDiagramHomotopy_paths R d h).2.trans
      (dgOdotMilnorNuNullDiagonalDiagramHomotopy_paths R d h).2.symm

/-- 概要：元上下二胞体の最初の側面はいずれも同じ全関手の可逆比較。
方針：元零角左辺・元包含辺の実ホモトピーの可逆性を使う。
規約：元側面を変えない。使われ方：全 prism 比較の境界の可逆性。 -/
lemma dgOdotMilnorNuNullPrismFirstHomotopy_isInvertible (j : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (dgOdotMilnorNuNullPrismFirstHomotopy R d h j)) := by
  fin_cases j
  · exact dgOdotMilnorNuZeroLeftDiagramHomotopy_isInvertible R d h
  · exact dgOdotMilnorNuInclusionDiagramHomotopy_isInvertible R d h

/-- 概要：元上下二胞体の最後の側面はいずれも同じ全関手の可逆比較。
方針：元零角上辺・元商辺の実ホモトピーの可逆性を使う。
規約：元側面を変えない。使われ方：全 prism 比較の境界の可逆性。 -/
lemma dgOdotMilnorNuNullPrismLastHomotopy_isInvertible (j : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (dgOdotMilnorNuNullPrismLastHomotopy R d h j)) := by
  fin_cases j
  · exact dgOdotMilnorNuZeroTopDiagramHomotopy_isInvertible R d h
  · exact dgOdotMilnorNuProjectionDiagramHomotopy_isInvertible R d h

end SerrePositivity.KST.SConstruction
