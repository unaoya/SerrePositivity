module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullLowerPrism
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.InnerAnodyneEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise

/-!
概要：元実／絶対下二胞体全体の同じ実比較ホモトピーの可逆性と Cat^perf 比較。
方針：元内ホーン制限を同じ指定境界比較へ照合し、充満忠実な制限で可逆性を戻す。
規約：元両二胞体と指定二短辺側面を保持。上二胞体との全比較は別工程。
使われ方：元核面の下二胞体の全関手同型。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：元下二胞体の全比較は元内ホーン上で同じ指定境界ホモトピーに一致する。
方針：元両端固定 prism の同じ内ホーン制限と因子交換の自然性を使う。
規約：元二短辺側面の全単体。使われ方：指定境界から全比較の可逆性の検出。 -/
lemma dgOdotMilnorNuNullLowerTriangleHomotopy_horn :
    ((horn 2 1).ι ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuNullLowerTriangleHomotopy R d h).h =
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornBoundaryInclusion 1 1 ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuNullPrismBoundaryHomotopy R d h 1).h := by
  have hs : ((horn 2 1).ι ▷ (Δ[1] : SSet.{u + 2})) ≫ (β_ Δ[2] Δ[1]).hom =
      (β_ (horn 2 1 : SSet.{u + 2}) Δ[1]).hom ≫ (Δ[1] ◁ (horn 2 1).ι) := rfl
  change ((horn 2 1).ι ▷ (Δ[1] : SSet.{u + 2})) ≫ (β_ Δ[2] Δ[1]).hom ≫
    dgOdotMilnorNuNullLowerPrism R d h = _
  rw [← Category.assoc, hs, Category.assoc,
    (dgOdotMilnorNuNullLowerPrism_restrictions R d h).1]
  let exchange (f : (horn 2 1 : SSet.{u + 2}) ⟶ boundary 2)
      (H : (boundary 2 : SSet.{u + 2}) ⊗ Δ[1] ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}) :
      (β_ (horn 2 1 : SSet.{u + 2}) Δ[1]).hom ≫ (Δ[1] ◁ f) ≫
        (β_ Δ[1] (boundary 2 : SSet.{u + 2})).hom ≫ H = (f ▷ Δ[1]) ≫ H := rfl
  exact exchange _ _

/-- 概要：元下二胞体全体の同じ比較ホモトピーは可逆な関手辺。
方針：内ホーン制限の充満忠実性と元境界比較の可逆性を使う。
規約：元の全ホモトピーを保持。使われ方：元両下二胞体の全関手同型。 -/
lemma dgOdotMilnorNuNullLowerTriangleHomotopy_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (dgOdotMilnorNuNullLowerTriangleHomotopy R d h)) := by
  let q := (pre ((horn 2 1 : (Δ[2] : SSet.{u + 2}).Subcomplex).ι)).app
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}
  letI : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.trivialKanFibration_pre_of_innerAnodyne _
    (innerAnodyneExtensions.horn_ι (show 0 < (1 : Fin 3) by decide)
      (show (1 : Fin 3) < Fin.last 2 by decide)) _
  have hq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful q :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration q).isFullyFaithful
  apply hq.reflects_isInvertibleEdge
  have hi := (dgOdotMilnorNuNullPrismBoundaryHomotopy_isInvertible R d h 1).map
    ((pre (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornBoundaryInclusion 1 1)).app _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1})
  have he : ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (dgOdotMilnorNuNullLowerTriangleHomotopy R d h)).map ((truncation 2).map q)).edge =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (dgOdotMilnorNuNullPrismBoundaryHomotopy R d h 1)).map ((truncation 2).map
          ((pre (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornBoundaryInclusion 1 1)).app _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}))).edge := by
    change q.app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (curry (dgOdotMilnorNuNullLowerTriangleHomotopy R d h).h)) =
        ((pre (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornBoundaryInclusion 1 1)).app _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}).app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (curry (dgOdotMilnorNuNullPrismBoundaryHomotopy R d h 1).h))
    rw [← SSet.yonedaEquiv_comp, ← SSet.yonedaEquiv_comp]
    change SSet.yonedaEquiv (curry (dgOdotMilnorNuNullLowerTriangleHomotopy R d h).h ≫
      (pre (horn 2 1).ι).app _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}) = _
    rw [curry_pre_app, curry_pre_app, dgOdotMilnorNuNullLowerTriangleHomotopy_horn]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr hi

/-- 概要：元実／絶対下二胞体の全単体を結ぶ同じ実全関手同型。
方針：同じ元可逆ホモトピーの辺の類を同型として取る。
規約：両二胞体を選び直さない。使われ方：元核面の下二胞体の全比較。 -/
def dgOdotMilnorNuNullLowerTriangleComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (SSet.yonedaEquiv.symm (dgOdotMilnorNuNullTriangle R d 1))
    (SSet.yonedaEquiv.symm (dgOdotMilnorNuAbsoluteNullTriangle R d h 1)) :=
  @asIso _ _ _ _ (SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgOdotMilnorNuNullLowerTriangleHomotopy R d h)))
      (dgOdotMilnorNuNullLowerTriangleHomotopy_isInvertible R d h)

/-- 概要：同じ元下二胞体の全比較を Cat^perf の元全二胞体へ戻す。
方針：同じ完備包含の充満忠実性と元全二単体の回収を使う。
規約：元実／絶対下二胞体を保持。使われ方：元 ν 核面の下二胞体の全比較。 -/
def dgOdotMilnorNuNullLowerPerfectTriangleComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ (dgOdotMilnorNuPerfectSequence R d h).presentation.square) := by
  apply perfectStableInfinityInclusion_isFullyFaithful.preimageFunctorIso
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ dgOdotMilnorPerfectNullSquare R d ≫
      dgKInputPerfectNu R ≫ perfectStableInfinityInclusion)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ perfectVerdierSquare (dgOdotMilnorNuPerfectSequence R d h) ≫
      perfectStableInfinityInclusion)
  rw [dgKInputPerfectNu_inclusion, perfectVerdierSquare_inclusion]
  simpa only [dgOdotMilnorNuNullTriangle, dgOdotMilnorNuAbsoluteNullTriangle,
    Equiv.symm_apply_apply] using dgOdotMilnorNuNullLowerTriangleComparison R d h

end SerrePositivity.KST.SConstruction
