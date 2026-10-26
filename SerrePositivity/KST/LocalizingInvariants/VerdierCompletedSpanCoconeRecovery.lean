module

public import SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery
public import SerrePositivity.KST.LocalizingInvariants.VerdierChosenTerminalRefinementMap
public import SerrePositivity.KST.LocalizingInvariants.CoconeFamilyCoreCriterion
public import SerrePositivity.KST.LocalizingInvariants.CorePreimageComparisonPrism

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
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

local instance completedCoconeFiniteLimits {X : SSet.{u}} [Quasicategory X] [IsStable X] :
    HasFiniteLimits X := hasFiniteLimits_of_isStable X

variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  {h : IsVerdierSequence i q} {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ B.obj) {z : B.obj _⦋0⦌}
  {S K : SSet.{u}} {j : S ⟶ K}

local notation "J" => join (Δ[n] : SSet) Δ[0]

variable {f : K ⟶ groupoidCompletion (fixedMarkedSpans B.obj (weakEquivalences i)
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
        z)}
  {a : S ⟶ groupoidCompletion (fixedMarkedSpans B.obj (weakEquivalences i)
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
        z)}
  {H : SSet.Homotopy a (j ≫ f)}

/-- 同じ回収済み実分母を使う、一様前段と写像円柱全体の実余錐。 -/
structure VerdierCompletedSpanCoconeRecovery
    (d : VerdierCompletedSpanBoundaryRecovery h
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
        z j f H) where
  single : (Δ[n] : SSet.{u}) ⟶ pullbackDiagrams B.obj
  single_projection : single ≫ pullbackProjection B.obj = simplexTerminalCospanFamily D
    ((joinStdSimplexIso 0 0).inv ≫ d.denominator.val.val)
    (verdierDenominatorDiagram_target i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
        d.denominator)
  single_terminal : single.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
    terminalPullbackColumnVertex ((joinStdSimplexIso 0 0).inv ≫ d.denominator.val.val)
  prefixDenominator : Truncated.Edge (X := (truncation 2).obj ((ihom Δ[n]).obj B.obj))
    (functorVertex (terminalRefinementSourceDiagram single)) (functorVertex D)
  prefixDenominator_mem : prefixDenominator.edge ∈
    (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌)
  prefixDenominator_edge : prefixDenominator.edge =
    (squareLeftArrow (terminalRefinementSquare single)).edge
  prefixDenominator_last : (evaluateFunctorAt (Y := B.obj)
    (stdSimplex.obj₀Equiv.symm (Fin.last n))).app (Opposite.op ⦋1⦌) prefixDenominator.edge =
      (roofPointSliceVertexEdge (SSet.yonedaEquiv.symm
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
        ) d.denominator.val).edge
  whole : finiteMappingCylinder j ⟶ (ihom J).obj B.obj
  whole_prefix : whole ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj =
    SSet.const (functorVertex (terminalRefinementSourceDiagram single))
  whole_next : whole ≫ (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app B.obj =
    verdierSpanFamilyNumeratorArrow i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
        z
      (d.whole ≫ vertexFiberι (verdierDenominatorSpanProjection i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
        z) d.denominator) ≫
      (pre (joinStdSimplexIso 0 0).hom).app B.obj
  whole_apex : whole ≫ evaluateFunctorAt ((joinInr (Δ[n] : SSet.{u}) Δ[0]).app
    (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) = SSet.const z

/-- 回収済みの完成境界全体へ、一つの実 pullback と全 attachment を実代入する。 -/
lemma exists_verdierCompletedSpanCoconeRecovery
    (d : VerdierCompletedSpanBoundaryRecovery h
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
        z j f H) :
    Nonempty (VerdierCompletedSpanCoconeRecovery D d) := by
  obtain ⟨F, hFp, hFl⟩ := exists_simplexTerminalPullbackFamily D
    ((joinStdSimplexIso 0 0).inv ≫ d.denominator.val.val)
    (verdierDenominatorDiagram_target i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
        d.denominator)
  obtain ⟨t, ht, hlast, hraw⟩ :=
    exists_verdierChosenTerminalRefinementMap_with_edge h D d.denominator F hFp hFl
  let M := finiteMappingCylinder j
  let FM := parametricPullbackDiagramFamily (uniformTerminalRefinementSquare M F)
    (uniformTerminalRefinementSquare_isPullback M F)
  have hFM := uniformFiberPullbackFamily_terminal i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
        z d.denominator d.whole F hFl
  obtain ⟨W, hp, hn, hz⟩ := exists_verdierSpanCoconeFamily i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
        z
    (d.whole ≫ vertexFiberι (verdierDenominatorSpanProjection i
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
    whole_prefix := hp.trans (uniformTerminalRefinementSquare_prefix M F)
    whole_next := hn
    whole_apex := hz }⟩

namespace VerdierCompletedSpanCoconeRecovery
variable {D} {d : VerdierCompletedSpanBoundaryRecovery h
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
        z j f H}
  (c : VerdierCompletedSpanCoconeRecovery D d)

/-- 同じ写像円柱から制限した、元の実全余錐の境界 prism。 -/
def coconeHomotopy : SSet.Homotopy
    (finiteMappingCylinderSource j ≫ c.whole)
    (j ≫ (CategoryTheory.Limits.pushout.inr (prismEndpoint 1 S) j ≫ c.whole)) := by
  let V := functorHomotopyPostcomp (finiteMappingCylinderHomotopy j) c.whole
  exact { h := V.h, h₀ := V.h₀, h₁ := V.h₁.trans (Category.assoc _ _ _), rel := V.rel }

/-- 実全余錐の境界 prism の次辺は、回収した同じ実分母 fiber 内の全 prism。 -/
lemma coconeHomotopy_next : c.coconeHomotopy.h ≫
    (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app B.obj =
      verdierSpanFamilyNumeratorArrow i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
        z
        (d.nativeHomotopy.h ≫ vertexFiberι
          (verdierDenominatorSpanProjection i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
        z) d.denominator) ≫
        (pre (joinStdSimplexIso 0 0).hom).app B.obj := by
  change ((finiteMappingCylinderHomotopy j).h ≫ c.whole) ≫
    (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app B.obj = _
  rw [Category.assoc, c.whole_next, ← Category.assoc,
    ← verdierSpanFamilyNumeratorArrow_pre]
  simp only [VerdierCompletedSpanBoundaryRecovery.nativeHomotopy,
    functorHomotopyPostcomp, Category.assoc]

/-- 一様な前段と固定頂点を持つ同じ全余錐族は、元の圏ですべての辺を反転する。 -/
lemma invertsAllEdges : InvertsEdges c.whole Set.univ := by
  apply coconeFamily_invertsAllEdges_of_prefix_apex c.whole z _ c.whole_apex
  rw [c.whole_prefix]
  exact invertsEdges_const _ _ _ Set.univ

/-- 同じ全余錐を、商後 core の元の厳密逆像へ戻した全写像円柱。 -/
def simplexWhole : finiteMappingCylinder j ⟶
    (relativeFirstRowSimplex q (n + 1) : SSet.{u}) :=
  corePreimageLift ((ihom (Δ[n + 1] : SSet.{u})).map q.hom)
    (c.whole ≫ (pre (joinStdSimplexIso n 0).inv).app B.obj)
    ((c.invertsAllEdges.comp ((pre (joinStdSimplexIso n 0).inv).app B.obj)).comp
      ((ihom (Δ[n + 1] : SSet.{u})).map q.hom))

lemma simplexWhole_ι : c.simplexWhole ≫ (relativeFirstRowSimplex q (n + 1)).ι =
    c.whole ≫ (pre (joinStdSimplexIso n 0).inv).app B.obj :=
  corePreimageLift_ι _ _ _

/-- 完成 K 全族から回収された、元の第一行単体内の同じ実 K 全族。 -/
def simplexFamily : K ⟶ (relativeFirstRowSimplex q (n + 1) : SSet.{u}) :=
  CategoryTheory.Limits.pushout.inr (prismEndpoint 1 S) j ≫ c.simplexWhole

/-- 完成 S 境界から回収された、同じ実前段を持つ元の実 S 境界。 -/
def simplexBoundary : S ⟶ (relativeFirstRowSimplex q (n + 1) : SSet.{u}) :=
  finiteMappingCylinderSource j ≫ c.simplexWhole

/-- 回収した元の実境界から全族の制限への、同じ全 prism。 -/
def simplexHomotopy : SSet.Homotopy c.simplexBoundary (j ≫ c.simplexFamily) := by
  let V := functorHomotopyPostcomp (finiteMappingCylinderHomotopy j) c.simplexWhole
  exact { h := V.h, h₀ := V.h₀, h₁ := V.h₁.trans (Category.assoc _ _ _), rel := V.rel }

end VerdierCompletedSpanCoconeRecovery
end SerrePositivity.KST.LocalizingInvariants
