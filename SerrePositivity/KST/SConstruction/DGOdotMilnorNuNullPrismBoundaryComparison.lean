module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullPrismBoundaryHomotopy
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HomotopyInvertibility

/-!
概要：元指定三側面による同じ境界ホモトピー自体が可逆であることを示す。
方針：元三側面の可逆性を全境界の頂点で検出し、既存の点ごとの判定を使う。
規約：元ホモトピーの比較射を保持。内部二胞体の比較ではない。
使われ方：元全境界充填へ渡す可逆な境界比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：同じ元境界ホモトピーの各元側面の頂点での経路は可逆。
方針：元全側面の厳密回収で同じ可逆側面の成分へ戻す。
規約：指定された元経路。使われ方：同じ全境界比較の可逆性の検出。 -/
lemma dgOdotMilnorNuNullPrismBoundaryHomotopy_component (j : Fin 2) (i : Fin 3)
    (x : (Δ[1] : SSet.{u + 2}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
      (dgOdotMilnorNuNullPrismBoundaryHomotopy R d h j)
      ((boundary.ι i).app (Opposite.op ⦋0⦌) x)).toTruncated := by
  have component {f g : (Δ[1] : SSet.{u + 2}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}}
      (H : SSet.Homotopy f g)
      (hh : (boundary.ι i ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuNullPrismBoundaryHomotopy R d h j).h = H.h)
      (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
        (dgOdotMilnorNuNullPrismBoundaryHomotopy R d h j)
        ((boundary.ι i).app (Opposite.op ⦋0⦌) x)).toTruncated := by
    let z : (Δ[1] ⊗ Δ[1] : SSet.{u + 2}) _⦋1⦌ :=
      ((SSet.Truncated.Edge.id (X := (truncation 2).obj (Δ[1] : SSet.{u + 2})) x).edge,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.{u + 2}.edge)
    have he := congrArg (fun q : (Δ[1] ⊗ Δ[1] : SSet.{u + 2}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} =>
      q.app (Opposite.op ⦋1⦌) z) hh
    have hid : (boundary.ι i).app (Opposite.op ⦋1⦌)
        (SSet.Truncated.Edge.id (X := (truncation 2).obj (Δ[1] : SSet.{u + 2})) x).edge =
        (SSet.Truncated.Edge.id (X := (truncation 2).obj (boundary 2 : SSet.{u + 2}))
          ((boundary.ι i).app (Opposite.op ⦋0⦌) x)).edge := by
      rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map (boundary.ι i) x 1
    change (dgOdotMilnorNuNullPrismBoundaryHomotopy R d h j).h.app (Opposite.op ⦋1⦌)
      ((boundary.ι i).app (Opposite.op ⦋1⦌)
        (SSet.Truncated.Edge.id (X := (truncation 2).obj (Δ[1] : SSet.{u + 2})) x).edge,
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) = _ at he
    rw [hid] at he
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
      (dgOdotMilnorNuNullPrismBoundaryHomotopy R d h j)
      ((boundary.ι i).app (Opposite.op ⦋0⦌) x)).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).edge at he
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyVertex_isInvertible_of_functorEdge H hi x)
  fin_cases i
  · exact component (dgOdotMilnorNuNullPrismLastHomotopy R d h j)
      (dgOdotMilnorNuNullPrismSideBoundary_faces R d h j 0)
      (dgOdotMilnorNuNullPrismLastHomotopy_isInvertible R d h j)
  · exact component (dgOdotMilnorNuNullDiagonalDiagramHomotopy R d h)
      (dgOdotMilnorNuNullPrismSideBoundary_faces R d h j 1)
      (dgOdotMilnorNuNullDiagonalDiagramHomotopy_isInvertible R d h)
  · exact component (dgOdotMilnorNuNullPrismFirstHomotopy R d h j)
      (dgOdotMilnorNuNullPrismSideBoundary_faces R d h j 2)
      (dgOdotMilnorNuNullPrismFirstHomotopy_isInvertible R d h j)

/-- 概要：元指定三側面による同じ全境界ホモトピーは可逆な関手辺。
方針：全三頂点を元側面の像として回収し、元側面成分で可逆性を検出する。
規約：元のホモトピーを変更しない。使われ方：指定境界比較の可逆性。 -/
lemma dgOdotMilnorNuNullPrismBoundaryHomotopy_isInvertible (j : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (dgOdotMilnorNuNullPrismBoundaryHomotopy R d h j)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorEdgeOfSimplicialHomotopy_isInvertible_of_pointwise
  intro k
  have cover : ∃ (i : Fin 3) (x : (Δ[1] : SSet.{u + 2}) _⦋0⦌),
      (boundary.ι i).app (Opposite.op ⦋0⦌) x = k := by
    rcases k with ⟨k, hk⟩
    obtain ⟨a, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective k
    fin_cases a
    · refine ⟨2, stdSimplex.obj₀Equiv.symm 0, ?_⟩
      apply Subtype.ext
      apply SSet.stdSimplex.ext
      intro b
      fin_cases b
      rfl
    · refine ⟨2, stdSimplex.obj₀Equiv.symm 1, ?_⟩
      apply Subtype.ext
      apply SSet.stdSimplex.ext
      intro b
      fin_cases b
      rfl
    · refine ⟨0, stdSimplex.obj₀Equiv.symm 1, ?_⟩
      apply Subtype.ext
      apply SSet.stdSimplex.ext
      intro b
      fin_cases b
      rfl
  obtain ⟨i, x, rfl⟩ := cover
  exact dgOdotMilnorNuNullPrismBoundaryHomotopy_component R d h j i x

/-- 概要：元実／絶対二胞体の元全境界を結ぶ同じ指定ホモトピーの全関手同型。
方針：同じ可逆関手辺の元の類を同型として取る。
規約：順方向の射は同じ元境界ホモトピー。使われ方：全境界充填の可逆比較。 -/
def dgOdotMilnorNuNullPrismBoundaryComparison (j : Fin 2) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((boundary 2).ι ≫ SSet.yonedaEquiv.symm (dgOdotMilnorNuNullTriangle R d j))
    ((boundary 2).ι ≫ SSet.yonedaEquiv.symm (dgOdotMilnorNuAbsoluteNullTriangle R d h j)) :=
  @asIso _ _ _ _ (SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgOdotMilnorNuNullPrismBoundaryHomotopy R d h j)))
      (dgOdotMilnorNuNullPrismBoundaryHomotopy_isInvertible R d h j)

end SerrePositivity.KST.SConstruction
