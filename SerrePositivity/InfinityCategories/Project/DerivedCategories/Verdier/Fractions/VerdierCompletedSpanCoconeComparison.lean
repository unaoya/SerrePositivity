module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.CoconeFamilyTranspose
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierUniformCoconeComparison

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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison
end SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.LocalizingInvariants
variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  {h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q} {n : ℕ} {D : (Δ[n] : SSet.{u}) ⟶ B.obj} {z : B.obj _⦋0⦌}
  {S K : SSet.{u}} {j : S ⟶ K}


variable {f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i)
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
        z)}
  {a : S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i)
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
        z)}
  {H : SSet.Homotopy a (j ≫ f)}


variable {d : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery h
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z j f H}
  (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery D d)
  (G : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinder j ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj)

/-- 同じ評価円柱と前段・次辺比較を保つ、元の全商余錐への実比較辺。 -/
structure VerdierCompletedSpanCoconeComparison where
  image : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierUniformCoconeImage (h := h)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.simplicialHomotopy d.evaluationIso) G
  edge : Truncated.Edge (X := (truncation 2).obj
      ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0])).obj ((ihom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinder j)).obj C.obj)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinder j)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0]) C.obj
      (c.whole ≫ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0])).map q.hom)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinder j)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0]) C.obj image.initialFamily))
  isInvertible : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
    (X := (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0])).obj
      ((ihom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinder j)).obj C.obj)) edge
  prefix_eq : ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app
      ((ihom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinder j)).obj C.obj)).app (Opposite.op ⦋1⦌) edge.edge =
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.spanConstantPrefixEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinder j) q.hom c.prefixDenominator).edge
  last_eq : ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app
      ((ihom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinder j)).obj C.obj)).app (Opposite.op ⦋1⦌) edge.edge =
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierUniformSpanFractionHomotopy h
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z
      d.denominator d.whole)).map ((truncation 2).map
        ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).app
          ((ihom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinder j)).obj C.obj)))).edge)

/-- 完成境界の同じ実回収データへ、区間延長と全 attachment 比較を実適用する。 -/
lemma exists_verdierCompletedSpanCoconeComparison
    (hG : G ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (D ≫ q.hom)))
    (hGe : G ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app C.obj =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.completedBoundaryCylinderMap j f H ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionMappingComparison q.hom
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.inverts
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((pre (boundary 1).ι).app C.obj)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingBoundary
            (q.hom.app (Opposite.op ⦋0⦌)
              (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
            (q.hom.app (Opposite.op ⦋0⦌) z))) ≫
        (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).app C.obj) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison c G) := by
  obtain ⟨U⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.exists_verdierUniformCoconeImage (h := h)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.simplicialHomotopy d.evaluationIso) G hG hGe
  obtain ⟨l, hl, hp, hn⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.exists_verdierUniformCoconeInitialComparison
    c.prefixDenominator c.prefixDenominator_mem c.prefixDenominator_last
    c.whole c.whole_prefix c.whole_next U
  exact ⟨⟨U, l, hl, hp, hn⟩⟩

/-- 有限完成分数の指定境界から、実分母・一様前段・元商全比較を全て一括構成する。 -/
lemma exists_verdierFiniteCompletedSpanCoconeComparison [S.Finite] [K.Finite]
    (hG : G ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (D ≫ q.hom)))
    (hGe : G ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app C.obj =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.completedBoundaryCylinderMap j f H ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionMappingComparison q.hom
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.inverts
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((pre (boundary 1).ι).app C.obj)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingBoundary
            (q.hom.app (Opposite.op ⦋0⦌)
              (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
            (q.hom.app (Opposite.op ⦋0⦌) z))) ≫
        (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).app C.obj) :
    ∃ d₀ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery h
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z j f H,
      ∃ c₀ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery D d₀,
        Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison c₀ G) := by
  obtain ⟨d₀⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.exists_verdierCompletedSpanBoundaryRecovery h
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z j f H
  obtain ⟨c₀⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.exists_verdierCompletedSpanCoconeRecovery D d₀
  exact ⟨d₀, c₀, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.exists_verdierCompletedSpanCoconeComparison c₀ G hG hGe⟩

namespace VerdierCompletedSpanCoconeComparison

variable {c G} (w : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison c G)

/-- 同じ指定比較辺から、実回収全余錐と元の商全余錐の全関手同型を得る。 -/
def iso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (c.whole ≫ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0])).map q.hom) G := by
  have hi : IsIso (Truncated.HomotopyCategory.homMk w.edge) := w.isInvertible
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.spanFunctorIsoUnflip (asIso (Truncated.HomotopyCategory.homMk w.edge)) ≪≫ w.image.iso

/-- 元の第一行単体の商射に、そのまま同じ全比較を戻す。 -/
def simplexAmbientIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (c.simplexWhole ≫ relativeFirstRowSimplexQuotient q (n + 1) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom (Δ[n + 1] : SSet.{u})).obj C.obj)).ι)
    (G ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv).app C.obj) := by
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp w.iso ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv).app C.obj)
  have hs : c.simplexWhole ≫ relativeFirstRowSimplexQuotient q (n + 1) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom (Δ[n + 1] : SSet.{u})).obj C.obj)).ι =
      (c.whole ≫ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0])).map q.hom) ≫
        (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv).app C.obj := by
    rw [relativeFirstRowSimplexQuotient_ι, ← Category.assoc, c.simplexWhole_ι]
    rw [Category.assoc, ← (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv).naturality q.hom]
    exact (Category.assoc _ _ _).symm
  rw [hs]
  exact e

include w in
lemma target_invertsAllEdges : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges
    (G ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv).app C.obj) Set.univ :=
  ((invertsEdges_functorIso_iff w.iso Set.univ).mp
    (c.invertsAllEdges.comp ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0])).map q.hom))).comp
      ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv).app C.obj)

/-- 指定された元の全商余錐を、そのまま全単体図式の core へ戻した標的。 -/
def simplexTarget : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinder j ⟶
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom (Δ[n + 1] : SSet.{u})).obj C.obj) : SSet.{u}) :=
  allEdgesCoreLift (G ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv).app C.obj) w.target_invertsAllEdges

lemma simplexTarget_ι : w.simplexTarget ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom (Δ[n + 1] : SSet.{u})).obj C.obj)).ι =
      G ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv).app C.obj :=
  allEdgesCoreLift_ι _ _

/-- 元の第一行単体商射の像と、同じ元の全商族を core 内の全関手同型で接続する。 -/
def simplexIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (c.simplexWhole ≫ relativeFirstRowSimplexQuotient q (n + 1)) w.simplexTarget := by
  let F := c.simplexWhole ≫ relativeFirstRowSimplexQuotient q (n + 1)
  let ι := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom (Δ[n + 1] : SSet.{u})).obj C.obj)).ι
  have hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (F ≫ ι) Set.univ := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertsAllEdges_toKan F).comp ι
  let V := allEdgesCoreComparisonHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge w.simplexAmbientIso)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge_isInvertible w.simplexAmbientIso) hF w.target_invertsAllEdges
  have hs : allEdgesCoreLift (F ≫ ι) hF = F := by
    apply (cancel_mono ι).mp
    exact allEdgesCoreLift_ι _ _
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy V
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (allEdgesCoreLift (F ≫ ι) hF) w.simplexTarget at e
  rw [hs] at e
  exact e

/-! 以降の三つの比較は、同じ全写像円柱上の core 比較の制限。 -/

/-- 元の K 全族への比較。境界と同じ全比較を制限する。 -/
def simplexFamilyIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (c.simplexFamily ≫ relativeFirstRowSimplexQuotient q (n + 1))
    (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 S) j ≫ w.simplexTarget) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.simplexFamily, Category.assoc] using
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp w.simplexIso (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 S) j)

/-- 元の S 境界への比較。全族と同じ全比較を制限する。 -/
def simplexBoundaryIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (c.simplexBoundary ≫ relativeFirstRowSimplexQuotient q (n + 1))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinderSource j ≫ w.simplexTarget) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.simplexBoundary, Category.assoc] using
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp w.simplexIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinderSource j)

/-- 指定された元の全 prism への比較も、同じ全比較の prism 制限。 -/
def simplexPrismIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (c.simplexHomotopy.h ≫ relativeFirstRowSimplexQuotient q (n + 1))
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinderHomotopy j).h ≫ w.simplexTarget) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeRecovery.simplexHomotopy,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp, Category.assoc] using
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp w.simplexIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinderHomotopy j).h

end VerdierCompletedSpanCoconeComparison
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exists_verdierCompletedSpanCoconeComparison := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.exists_verdierCompletedSpanCoconeComparison

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exists_verdierFiniteCompletedSpanCoconeComparison := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.exists_verdierFiniteCompletedSpanCoconeComparison

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.casesOn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.ctorIdx := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.edge (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.edge := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.edge

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.image (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.image := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.image

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.isInvertible := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.isInvertible

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.iso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.iso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.iso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.last_eq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.last_eq

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.mk := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.noConfusionType := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.noConfusionType

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.prefix_eq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.prefix_eq

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.rec := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.recOn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.simplexAmbientIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.simplexAmbientIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.simplexAmbientIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.simplexBoundaryIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.simplexBoundaryIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.simplexBoundaryIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.simplexFamilyIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.simplexFamilyIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.simplexFamilyIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.simplexIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.simplexIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.simplexIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.simplexPrismIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.simplexPrismIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.simplexPrismIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.simplexTarget (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.simplexTarget := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.simplexTarget

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.simplexTarget_ι := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.simplexTarget_ι

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.target_invertsAllEdges := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.target_invertsAllEdges

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.iso._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.iso._proof_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.mk.inj := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.mk.injEq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.mk.sizeOf_spec

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.simplexAmbientIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.simplexAmbientIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.simplexAmbientIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.simplexAmbientIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.simplexBoundaryIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.simplexBoundaryIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.simplexFamilyIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.simplexFamilyIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.simplexFamilyIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.simplexFamilyIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.simplexFamilyIso._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.simplexFamilyIso._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.simplexIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.simplexIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.simplexIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.simplexIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.simplexIso._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.simplexIso._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.simplexIso._proof_4 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.simplexIso._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.simplexIso._proof_5 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.simplexIso._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.simplexIso._proof_6 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.simplexIso._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.simplexPrismIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.simplexPrismIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanCoconeComparison.simplexPrismIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanCoconeComparison.simplexPrismIso._proof_2
