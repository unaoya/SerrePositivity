module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.SimplexTerminalPullbackFamily
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CoconeFamilyCoreCriterion
public import SerrePositivity.KST.LocalizingInvariants.CorePreimageComparisonPrism
public import SerrePositivity.KST.LocalizingInvariants.SimplexTerminalPullbackFamily
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierChosenTerminalRefinementMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery

/-!
概要：完成分数の指定有限境界を、同じ実分母・一様前段・全余錐円柱へ接続する。
方針：回収した写像円柱全体の実次辺族へ、一つの終端 pullback と attachment を適用する。
規約：全族・境界・prism に同じ前段と実分母を使い、元の第一行単体内へ戻す。
使われ方：完成分数の有限境界回収から全単体の元の実境界を得る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery
end SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.LocalizingInvariants

local instance completedCoconeFiniteLimits {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasFiniteLimits_of_isStable X

variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  {h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q} {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ B.obj) {z : B.obj _⦋0⦌}
  {S K : SSet.{u}} {j : S ⟶ K}

local notation "J" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet) Δ[0]

variable {f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i)
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
        z)}
  {a : S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i)
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
        z)}
  {H : SSet.Homotopy a (j ≫ f)}

/-- 同じ回収済み実分母を使う、一様前段と写像円柱全体の実余錐。 -/
structure VerdierCompletedSpanCoconeRecovery
    (d : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery h
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
        z j f H) where
  single : (Δ[n] : SSet.{u}) ⟶ pullbackDiagrams B.obj
  single_projection : single ≫ pullbackProjection B.obj = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.simplexTerminalCospanFamily D
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ d.denominator.val.val)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorDiagram_target i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
        d.denominator)
  single_terminal : single.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
    terminalPullbackColumnVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ d.denominator.val.val)
  prefixDenominator : Truncated.Edge (X := (truncation 2).obj ((ihom Δ[n]).obj B.obj))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.terminalRefinementSourceDiagram single)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex D)
  prefixDenominator_mem : prefixDenominator.edge ∈
    (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌)
  prefixDenominator_edge : prefixDenominator.edge =
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareLeftArrow (terminalRefinementSquare single)).edge
  prefixDenominator_last : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := B.obj)
    (stdSimplex.obj₀Equiv.symm (Fin.last n))).app (Opposite.op ⦋1⦌) prefixDenominator.edge =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge (SSet.yonedaEquiv.symm
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
        ) d.denominator.val).edge
  whole : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinder j ⟶ (ihom J).obj B.obj
  whole_prefix : whole ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj =
    SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.terminalRefinementSourceDiagram single))
  whole_next : whole ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app B.obj =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanFamilyNumeratorArrow i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
        z
      (d.whole ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
        z) d.denominator) ≫
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).app B.obj
  whole_apex : whole ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}) Δ[0]).app
    (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) = SSet.const z

/-- 回収済みの完成境界全体へ、一つの実 pullback と全 attachment を実代入する。 -/
lemma exists_verdierCompletedSpanCoconeRecovery
    (d : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery h
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
        z j f H) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery D d) := by
  obtain ⟨F, hFp, hFl⟩ := exists_simplexTerminalPullbackFamily D
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ d.denominator.val.val)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorDiagram_target i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
        d.denominator)
  obtain ⟨t, ht, hlast, hraw⟩ :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.exists_verdierChosenTerminalRefinementMap_with_edge h D d.denominator F hFp hFl
  let M := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinder j
  let FM := parametricPullbackDiagramFamily (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.uniformTerminalRefinementSquare M F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.uniformTerminalRefinementSquare_isPullback M F)
  have hFM := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.uniformFiberPullbackFamily_terminal i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
        z d.denominator d.whole F hFl
  obtain ⟨W, hp, hn, hz⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.exists_verdierSpanCoconeFamily i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
        z
    (d.whole ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
        z) d.denominator) FM hFM
  exact ⟨{
    single := F
    single_projection := hFp
    single_terminal := hFl
    prefixDenominator := t
    prefixDenominator_mem := ht
    prefixDenominator_edge := hraw
    prefixDenominator_last := hlast
    whole := W
    whole_prefix := hp.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.uniformTerminalRefinementSquare_prefix M F)
    whole_next := hn
    whole_apex := hz }⟩

namespace VerdierCompletedSpanCoconeRecovery

variable {D} {d : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery h
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
        z j f H}
  (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery D d)

/-- 同じ写像円柱から制限した、元の実全余錐の境界 prism。 -/
def coconeHomotopy : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinderSource j ≫ c.whole)
    (j ≫ (CategoryTheory.Limits.pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 S) j ≫ c.whole)) := by
  let V := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinderHomotopy j) c.whole
  exact { h := V.h, h₀ := V.h₀, h₁ := V.h₁.trans (Category.assoc _ _ _), rel := V.rel }

/-- 実全余錐の境界 prism の次辺は、回収した同じ実分母 fiber 内の全 prism。 -/
lemma coconeHomotopy_next : c.coconeHomotopy.h ≫
    (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app B.obj =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanFamilyNumeratorArrow i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
        z
        (d.nativeHomotopy.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
        z) d.denominator) ≫
        (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).app B.obj := by
  change ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinderHomotopy j).h ≫ c.whole) ≫
    (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app B.obj = _
  rw [Category.assoc, c.whole_next, ← Category.assoc,
    ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanFamilyNumeratorArrow_pre]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.nativeHomotopy,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp, Category.assoc]

/-- 一様な前段と固定頂点を持つ同じ全余錐族は、元の圏ですべての辺を反転する。 -/
lemma invertsAllEdges : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges c.whole Set.univ := by
  apply coconeFamily_invertsAllEdges_of_prefix_apex c.whole z _ c.whole_apex
  rw [c.whole_prefix]
  exact invertsEdges_const _ _ _ Set.univ

/-- 同じ全余錐を、商後 core の元の厳密逆像へ戻した全写像円柱。 -/
def simplexWhole : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinder j ⟶
    (relativeFirstRowSimplex q (n + 1) : SSet.{u}) :=
  corePreimageLift ((ihom (Δ[n + 1] : SSet.{u})).map q.hom)
    (c.whole ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv).app B.obj)
    ((c.invertsAllEdges.comp ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv).app B.obj)).comp
      ((ihom (Δ[n + 1] : SSet.{u})).map q.hom))

lemma simplexWhole_ι : c.simplexWhole ≫ (relativeFirstRowSimplex q (n + 1)).ι =
    c.whole ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv).app B.obj :=
  corePreimageLift_ι _ _ _

/-- 完成 K 全族から回収された、元の第一行単体内の同じ実 K 全族。 -/
def simplexFamily : K ⟶ (relativeFirstRowSimplex q (n + 1) : SSet.{u}) :=
  CategoryTheory.Limits.pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 S) j ≫ c.simplexWhole

/-- 完成 S 境界から回収された、同じ実前段を持つ元の実 S 境界。 -/
def simplexBoundary : S ⟶ (relativeFirstRowSimplex q (n + 1) : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinderSource j ≫ c.simplexWhole

/-- 回収した元の実境界から全族の制限への、同じ全 prism。 -/
def simplexHomotopy : SSet.Homotopy c.simplexBoundary (j ≫ c.simplexFamily) := by
  let V := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinderHomotopy j) c.simplexWhole
  exact { h := V.h, h₀ := V.h₀, h₁ := V.h₁.trans (Category.assoc _ _ _), rel := V.rel }

end VerdierCompletedSpanCoconeRecovery
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
