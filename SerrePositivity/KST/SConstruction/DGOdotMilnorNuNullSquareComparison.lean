module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullSquareHomotopy
/-!
概要：元の実 ν 核零化四角形全体と絶対完備化付き核列の実全図式同型。
方針：元上下比較の可逆性を保ち、同じ共有対角に沿う貼り合わせへ反映する。
規約：元の両二胞体を保持。LT の右面・外周・全長方形の比較とは区別する。
使われ方：指定三境界付き核面の全比較の接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
private lemma nullSquarePointwise {A X : SSet.{u}} [Quasicategory X]
    {f g : A ⟶ X} (H : SSet.Homotopy f g)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) (x : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).toTruncated := by
  have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.simplicialHomotopyOfFunctorEdge_vertex_isInvertible
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) hi x
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr ?_).mp hx
  change (uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry H.h)))).app
      (Opposite.op ⦋1⦌) _ = H.h.app (Opposite.op ⦋1⦌) _
  rw [Equiv.symm_apply_apply, uncurry_curry]
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)
/-- 概要：元全四角形の下三角形比較は元全比較の類を保つので可逆。
方針：代表修正の全三角形の類の等号で可逆性を回収する。
規約：元の比較代表。使われ方：元四角形全体の可逆性。 -/
lemma dgOdotMilnorNuNullAlignedLowerTriangleHomotopy_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (dgOdotMilnorNuNullAlignedLowerTriangleHomotopy R d h)) := by
  change IsIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
    (dgOdotMilnorNuNullAlignedLowerTriangleHomotopy R d h)))
  rw [dgOdotMilnorNuNullAlignedLowerTriangleHomotopy_class]
  exact dgOdotMilnorNuNullLowerTriangleHomotopy_isInvertible R d h
/-- 概要：元実／絶対全四角形の同じ実比較ホモトピーは可逆な関手辺。
方針：元上・下三角形比較の点ごとの可逆性を元 pushout 上で検出する。
規約：元の実全射を保持。使われ方：元核面の全図式同型。 -/
lemma dgOdotMilnorNuNullSquareHomotopy_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (dgOdotMilnorNuNullSquareHomotopy R d h)) := by
  have hu : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (dgOdotMilnorNuNullSquareUpperHomotopy R d h)) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
      (e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgOdotMilnorNuNullUpperTriangleHomotopy R d h))
      (f := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgOdotMilnorNuNullSquareUpperHomotopy R d h))
      rfl).mp (dgOdotMilnorNuNullUpperTriangleHomotopy_isInvertible R d h)
  have hl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (dgOdotMilnorNuNullSquareLowerHomotopy R d h)) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
      (e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (dgOdotMilnorNuNullAlignedLowerTriangleHomotopy R d h))
      (f := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgOdotMilnorNuNullSquareLowerHomotopy R d h))
      rfl).mp (dgOdotMilnorNuNullAlignedLowerTriangleHomotopy_isInvertible R d h)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorEdgeOfSimplicialHomotopy_isInvertible_of_pointwise
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pushoutHomotopy_isInvertible _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout
    (dgOdotMilnorNuNullSquareHomotopy R d h)
    (dgOdotMilnorNuNullSquareUpperHomotopy R d h)
    (dgOdotMilnorNuNullSquareLowerHomotopy R d h)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pushoutHomotopy_inl _ _ _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pushoutHomotopy_inr _ _ _ _)
    (nullSquarePointwise _ hu) (nullSquarePointwise _ hl)
/-- 概要：元実 ν 核面と元絶対零化四角形の実全関手同型。
方針：同じ元可逆ホモトピーの辺の類を同型として取る。
規約：上下両二胞体を保持。使われ方：元核列の全図式比較。 -/
def dgOdotMilnorNuNullSquareComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R)
    (perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h)) :=
  @asIso _ _ _ _ (SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgOdotMilnorNuNullSquareHomotopy R d h)))
      (dgOdotMilnorNuNullSquareHomotopy_isInvertible R d h)
/-- 概要：元実／絶対核四角形全体の比較を、同じ元 Cat^perf 四角形へ戻す。
方針：同じ完備包含の充満忠実性と元全四角形の回収を使う。
規約：元実面と元絶対提示を保持。使われ方：Sp 正本への核面の全比較接続。 -/
def dgOdotMilnorNuNullPerfectSquareComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R)
    (dgOdotMilnorNuPerfectSequence R d h).presentation.square := by
  apply perfectStableInfinityInclusion_isFullyFaithful.preimageFunctorIso
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R ≫ perfectStableInfinityInclusion)
    (perfectVerdierSquare (dgOdotMilnorNuPerfectSequence R d h) ≫ perfectStableInfinityInclusion)
  rw [dgKInputPerfectNu_inclusion, perfectVerdierSquare_inclusion]
  exact dgOdotMilnorNuNullSquareComparison R d h
end SerrePositivity.KST.SConstruction
