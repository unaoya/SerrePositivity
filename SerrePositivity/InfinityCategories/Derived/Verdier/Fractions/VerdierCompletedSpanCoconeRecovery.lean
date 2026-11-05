module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Stable.Quasicategory.SimplexTerminalPullbackFamily
public import SerrePositivity.KST.LocalizingInvariants.CoconeFamilyCoreCriterion
public import SerrePositivity.KST.LocalizingInvariants.CorePreimageComparisonPrism
public import SerrePositivity.KST.LocalizingInvariants.SimplexTerminalPullbackFamily
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierChosenTerminalRefinementMap
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery

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
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.LocalizingInvariants

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
open SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery
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
end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.completedCoconeFiniteLimits := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.completedCoconeFiniteLimits

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exists_verdierCompletedSpanCoconeRecovery := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.exists_verdierCompletedSpanCoconeRecovery

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.casesOn := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.coconeHomotopy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.coconeHomotopy := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.coconeHomotopy

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.coconeHomotopy_next := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.coconeHomotopy_next

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.ctorIdx := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.ctorIdx

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.invertsAllEdges := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.invertsAllEdges

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.mk := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.noConfusion := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.noConfusionType := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.prefixDenominator (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.prefixDenominator := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.prefixDenominator

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.prefixDenominator_edge := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.prefixDenominator_edge

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.prefixDenominator_last := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.prefixDenominator_last

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.prefixDenominator_mem := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.prefixDenominator_mem

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.rec := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.recOn := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.simplexBoundary (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.simplexBoundary := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.simplexBoundary

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.simplexFamily (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.simplexFamily := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.simplexFamily

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.simplexHomotopy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.simplexHomotopy := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.simplexHomotopy

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.simplexWhole (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.simplexWhole := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.simplexWhole

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.simplexWhole_ι := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.simplexWhole_ι

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.single (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.single := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.single

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.single_projection := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.single_projection

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.single_terminal := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.single_terminal

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.whole (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.whole := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.whole

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.whole_apex := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.whole_apex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.whole_next := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.whole_next

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.whole_prefix := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.whole_prefix

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.coconeHomotopy._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.coconeHomotopy._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.coconeHomotopy._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.coconeHomotopy._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.coconeHomotopy._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.coconeHomotopy._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.coconeHomotopy._proof_4 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.coconeHomotopy._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.coconeHomotopy._proof_5 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.coconeHomotopy._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.coconeHomotopy._proof_6 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.coconeHomotopy._proof_6

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.mk.inj := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.mk.injEq := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.mk.sizeOf_spec

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.simplexHomotopy._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.simplexHomotopy._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.simplexHomotopy._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.simplexHomotopy._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.simplexHomotopy._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.simplexHomotopy._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeRecovery.simplexWhole._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.simplexWhole._proof_1
