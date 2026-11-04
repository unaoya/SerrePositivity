module

public import SerrePositivity.InfinityCategories.Stable.Quasicategory.CoconeFamilyTranspose
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeComparison

/-!
概要：完成境界から回収した実全余錐を、指定された元の商余錐全族へ接続する。
方針：同じ評価同型を区間延長へ渡し、実分母の終端成分から共有経路を証明して貼る。
規約：元の商全族・同じ実分母・次辺族・全写像円柱を保持し、全比較辺の両制限を公開する。
使われ方：c5 の完成側有限境界を元の第一行単体比較へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  {h : IsVerdierSequence i q} {n : ℕ} {D : (Δ[n] : SSet.{u}) ⟶ B.obj} {z : B.obj _⦋0⦌}
  {S K : SSet.{u}} {j : S ⟶ K}


variable {f : K ⟶ groupoidCompletion (fixedMarkedSpans B.obj (weakEquivalences i)
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
        z)}
  {a : S ⟶ groupoidCompletion (fixedMarkedSpans B.obj (weakEquivalences i)
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
        z)}
  {H : SSet.Homotopy a (j ≫ f)}


variable {d : VerdierCompletedSpanBoundaryRecovery h
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z j f H}
  (c : VerdierCompletedSpanCoconeRecovery D d)
  (G : finiteMappingCylinder j ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj)

/-- 同じ評価円柱と前段・次辺比較を保つ、元の全商余錐への実比較辺。 -/
structure VerdierCompletedSpanCoconeComparison where
  image : VerdierUniformCoconeImage (h := h)
    (FunctorIso.simplicialHomotopy d.evaluationIso) G
  edge : Truncated.Edge (X := (truncation 2).obj
      ((ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj ((ihom (finiteMappingCylinder j)).obj C.obj)))
    (functorVertex (internalHomFlipHomEquiv (finiteMappingCylinder j)
      (join (Δ[n] : SSet.{u}) Δ[0]) C.obj
      (c.whole ≫ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).map q.hom)))
    (functorVertex (internalHomFlipHomEquiv (finiteMappingCylinder j)
      (join (Δ[n] : SSet.{u}) Δ[0]) C.obj image.initialFamily))
  isInvertible : IsInvertibleEdge
    (X := (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj
      ((ihom (finiteMappingCylinder j)).obj C.obj)) edge
  prefix_eq : ((pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app
      ((ihom (finiteMappingCylinder j)).obj C.obj)).app (Opposite.op ⦋1⦌) edge.edge =
    (spanConstantPrefixEdge (finiteMappingCylinder j) q.hom c.prefixDenominator).edge
  last_eq : ((pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app
      ((ihom (finiteMappingCylinder j)).obj C.obj)).app (Opposite.op ⦋1⦌) edge.edge =
    (((functorEdgeOfSimplicialHomotopy (verdierUniformSpanFractionHomotopy h
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z
      d.denominator d.whole)).map ((truncation 2).map
        ((pre (joinStdSimplexIso 0 0).hom).app
          ((ihom (finiteMappingCylinder j)).obj C.obj)))).edge)

/-- 完成境界の同じ実回収データへ、区間延長と全 attachment 比較を実適用する。 -/
lemma exists_verdierCompletedSpanCoconeComparison
    (hG : G ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj =
      SSet.const (functorVertex (D ≫ q.hom)))
    (hGe : G ≫ (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app C.obj =
      (completedBoundaryCylinderMap j f H ≫ fractionMappingComparison q.hom
        (weakEquivalences i) h.inverts
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) ≫
        vertexFiberι ((pre (boundary 1).ι).app C.obj)
          (functorVertex (intervalMappingBoundary
            (q.hom.app (Opposite.op ⦋0⦌)
              (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
            (q.hom.app (Opposite.op ⦋0⦌) z))) ≫
        (pre (joinStdSimplexIso 0 0).hom).app C.obj) :
    Nonempty (VerdierCompletedSpanCoconeComparison c G) := by
  obtain ⟨U⟩ := exists_verdierUniformCoconeImage (h := h)
    (FunctorIso.simplicialHomotopy d.evaluationIso) G hG hGe
  obtain ⟨l, hl, hp, hn⟩ := exists_verdierUniformCoconeInitialComparison
    c.prefixDenominator c.prefixDenominator_mem c.prefixDenominator_last
    c.whole c.whole_prefix c.whole_next U
  exact ⟨⟨U, l, hl, hp, hn⟩⟩

/-- 有限完成分数の指定境界から、実分母・一様前段・元商全比較を全て一括構成する。 -/
lemma exists_verdierFiniteCompletedSpanCoconeComparison [S.Finite] [K.Finite]
    (hG : G ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj =
      SSet.const (functorVertex (D ≫ q.hom)))
    (hGe : G ≫ (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app C.obj =
      (completedBoundaryCylinderMap j f H ≫ fractionMappingComparison q.hom
        (weakEquivalences i) h.inverts
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) ≫
        vertexFiberι ((pre (boundary 1).ι).app C.obj)
          (functorVertex (intervalMappingBoundary
            (q.hom.app (Opposite.op ⦋0⦌)
              (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
            (q.hom.app (Opposite.op ⦋0⦌) z))) ≫
        (pre (joinStdSimplexIso 0 0).hom).app C.obj) :
    ∃ d₀ : VerdierCompletedSpanBoundaryRecovery h
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z j f H,
      ∃ c₀ : VerdierCompletedSpanCoconeRecovery D d₀,
        Nonempty (VerdierCompletedSpanCoconeComparison c₀ G) := by
  obtain ⟨d₀⟩ := exists_verdierCompletedSpanBoundaryRecovery h
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z j f H
  obtain ⟨c₀⟩ := exists_verdierCompletedSpanCoconeRecovery D d₀
  exact ⟨d₀, c₀, exists_verdierCompletedSpanCoconeComparison c₀ G hG hGe⟩

namespace VerdierCompletedSpanCoconeComparison
variable {c G} (w : VerdierCompletedSpanCoconeComparison c G)

/-- 同じ指定比較辺から、実回収全余錐と元の商全余錐の全関手同型を得る。 -/
def iso : FunctorIso (c.whole ≫ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).map q.hom) G := by
  have hi : IsIso (Truncated.HomotopyCategory.homMk w.edge) := w.isInvertible
  exact spanFunctorIsoUnflip (asIso (Truncated.HomotopyCategory.homMk w.edge)) ≪≫ w.image.iso

/-- 元の第一行単体の商射に、そのまま同じ全比較を戻す。 -/
def simplexAmbientIso : FunctorIso
    (c.simplexWhole ≫ relativeFirstRowSimplexQuotient q (n + 1) ≫
      (quasicategoryCore ((ihom (Δ[n + 1] : SSet.{u})).obj C.obj)).ι)
    (G ≫ (pre (joinStdSimplexIso n 0).inv).app C.obj) := by
  have e := FunctorIso.postcomp w.iso ((pre (joinStdSimplexIso n 0).inv).app C.obj)
  have hs : c.simplexWhole ≫ relativeFirstRowSimplexQuotient q (n + 1) ≫
      (quasicategoryCore ((ihom (Δ[n + 1] : SSet.{u})).obj C.obj)).ι =
      (c.whole ≫ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).map q.hom) ≫
        (pre (joinStdSimplexIso n 0).inv).app C.obj := by
    rw [relativeFirstRowSimplexQuotient_ι, ← Category.assoc, c.simplexWhole_ι]
    rw [Category.assoc, ← (pre (joinStdSimplexIso n 0).inv).naturality q.hom]
    exact (Category.assoc _ _ _).symm
  rw [hs]
  exact e

include w in
lemma target_invertsAllEdges : InvertsEdges
    (G ≫ (pre (joinStdSimplexIso n 0).inv).app C.obj) Set.univ :=
  ((invertsEdges_functorIso_iff w.iso Set.univ).mp
    (c.invertsAllEdges.comp ((ihom (join (Δ[n] : SSet.{u}) Δ[0])).map q.hom))).comp
      ((pre (joinStdSimplexIso n 0).inv).app C.obj)

/-- 指定された元の全商余錐を、そのまま全単体図式の core へ戻した標的。 -/
def simplexTarget : finiteMappingCylinder j ⟶
    (quasicategoryCore ((ihom (Δ[n + 1] : SSet.{u})).obj C.obj) : SSet.{u}) :=
  allEdgesCoreLift (G ≫ (pre (joinStdSimplexIso n 0).inv).app C.obj) w.target_invertsAllEdges

lemma simplexTarget_ι : w.simplexTarget ≫
    (quasicategoryCore ((ihom (Δ[n + 1] : SSet.{u})).obj C.obj)).ι =
      G ≫ (pre (joinStdSimplexIso n 0).inv).app C.obj :=
  allEdgesCoreLift_ι _ _

/-- 元の第一行単体商射の像と、同じ元の全商族を core 内の全関手同型で接続する。 -/
def simplexIso : FunctorIso
    (c.simplexWhole ≫ relativeFirstRowSimplexQuotient q (n + 1)) w.simplexTarget := by
  let F := c.simplexWhole ≫ relativeFirstRowSimplexQuotient q (n + 1)
  let ι := (quasicategoryCore ((ihom (Δ[n + 1] : SSet.{u})).obj C.obj)).ι
  have hF : InvertsEdges (F ≫ ι) Set.univ := (invertsAllEdges_toKan F).comp ι
  let V := allEdgesCoreComparisonHomotopy (FunctorIso.edge w.simplexAmbientIso)
    (FunctorIso.edge_isInvertible w.simplexAmbientIso) hF w.target_invertsAllEdges
  have hs : allEdgesCoreLift (F ≫ ι) hF = F := by
    apply (cancel_mono ι).mp
    exact allEdgesCoreLift_ι _ _
  have e := functorIsoOfSimplicialHomotopy V
  change FunctorIso (allEdgesCoreLift (F ≫ ι) hF) w.simplexTarget at e
  rw [hs] at e
  exact e

/-! 以降の三つの比較は、同じ全写像円柱上の core 比較の制限。 -/

/-- 元の K 全族への比較。境界と同じ全比較を制限する。 -/
def simplexFamilyIso : FunctorIso
    (c.simplexFamily ≫ relativeFirstRowSimplexQuotient q (n + 1))
    (pushout.inr (prismEndpoint 1 S) j ≫ w.simplexTarget) := by
  simpa only [VerdierCompletedSpanCoconeRecovery.simplexFamily, Category.assoc] using
    FunctorIso.precomp w.simplexIso (pushout.inr (prismEndpoint 1 S) j)

/-- 元の S 境界への比較。全族と同じ全比較を制限する。 -/
def simplexBoundaryIso : FunctorIso
    (c.simplexBoundary ≫ relativeFirstRowSimplexQuotient q (n + 1))
    (finiteMappingCylinderSource j ≫ w.simplexTarget) := by
  simpa only [VerdierCompletedSpanCoconeRecovery.simplexBoundary, Category.assoc] using
    FunctorIso.precomp w.simplexIso (finiteMappingCylinderSource j)

/-- 指定された元の全 prism への比較も、同じ全比較の prism 制限。 -/
def simplexPrismIso : FunctorIso
    (c.simplexHomotopy.h ≫ relativeFirstRowSimplexQuotient q (n + 1))
    ((finiteMappingCylinderHomotopy j).h ≫ w.simplexTarget) := by
  simpa only [VerdierCompletedSpanCoconeRecovery.simplexHomotopy,
    functorHomotopyPostcomp, Category.assoc] using
    FunctorIso.precomp w.simplexIso (finiteMappingCylinderHomotopy j).h

end VerdierCompletedSpanCoconeComparison
end SerrePositivity.KST.LocalizingInvariants
