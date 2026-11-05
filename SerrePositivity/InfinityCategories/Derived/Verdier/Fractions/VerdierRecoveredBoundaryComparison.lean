module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Stable.Quasicategory.CoconeFamilyTranspose
public import SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeFunctorCoreRestriction
public import SerrePositivity.KST.LocalizingInvariants.CoconeFamilyCoreComparison
public import SerrePositivity.InfinityCategories.Derived.Localization.SimplexAttachmentEquivalences
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryPrefixPath
public import SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoreCylinder
public import SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredQuotientCoconeCylinder
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierSimplexCompletionComparison

/-!
概要：元の実境界円柱の商像と商余錐円柱の境界を、同じ二胞体を保持して全図式比較する。
方針：実前段左辺と元の分数比較辺の共有全経路を実代入し、相対 attachment へ直接貼る。
規約：次辺比較を Hom 類から選び直さず、元の分数評価二胞体の一次単体を保持する。
使われ方：指定した全境界比較を K 全体の比較へ延長する工程の実境界。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison
end SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.LocalizingInvariants

variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  {h : IsVerdierSequence i q} {n : ℕ} {D : (Δ[n] : SSet.{u}) ⟶ B.obj}
  {z : B.obj _⦋0⦌} {K : SSet.{u}} {S : K.Subcomplex}
  {a : S.toSSet ⟶ verdierDenominatorSpanFamily i
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z}
  {f : K ⟶ intervalMappingSpace
    (q.hom.app (Opposite.op ⦋0⦌)
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
    (q.hom.app (Opposite.op ⦋0⦌) z)}
  {G : K ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj}

local notation "P" => S.toSSet ⊗ (Δ[1] : SSet)
local notation "J" => join (Δ[n] : SSet) Δ[0]

/-- 同じ実前段辺と同じ分数比較辺を制限に持つ、実境界円柱の全図式比較。 -/
structure VerdierRecoveredBoundaryComparison
    (r : VerdierFiniteMappingCoconeRecovery h D z S a f)
    (U : VerdierRecoveredQuotientCoconeCylinder r G) where
  edge : Truncated.Edge (X := (truncation 2).obj ((ihom J).obj ((ihom P).obj C.obj)))
    (functorVertex (internalHomFlipHomEquiv P J C.obj
      (r.cylinder.homotopy.h ≫ (ihom J).map q.hom)))
    (functorVertex (internalHomFlipHomEquiv P J C.obj ((S.ι ▷ Δ[1]) ≫ U.whole)))
  isInvertible : IsInvertibleEdge (X := (ihom J).obj ((ihom P).obj C.obj)) edge
  prefix_eq : ((pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app ((ihom P).obj C.obj)).app
      (Opposite.op ⦋1⦌) edge.edge =
    (((squareLeftArrow r.cylinderSquare).map ((truncation 2).map
      ((ihom (Δ[n] : SSet.{u})).map ((ihom P).map q.hom)))).edge)
  last_eq : ((pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app ((ihom P).obj C.obj)).app
      (Opposite.op ⦋1⦌) edge.edge =
    (((functorEdgeOfSimplicialHomotopy r.boundaryFractionHomotopy).map ((truncation 2).map
      ((pre (joinStdSimplexIso 0 0).hom).app ((ihom P).obj C.obj)))).edge)

/-- 回収済みの同じ二つの全円柱へ共有全経路を実代入し、指定二胞体を保持して貼る。 -/
lemma exists_verdierRecoveredBoundaryComparison
    (r : VerdierFiniteMappingCoconeRecovery h D z S a f)
    (U : VerdierRecoveredQuotientCoconeCylinder r G) :
    Nonempty (VerdierRecoveredBoundaryComparison r U) := by
  let F := internalHomFlipHomEquiv P J C.obj (r.cylinder.homotopy.h ≫ (ihom J).map q.hom)
  let T := internalHomFlipHomEquiv P J C.obj ((S.ι ▷ Δ[1]) ≫ U.whole)
  let A₀ := (squareLeftArrow r.cylinderSquare).map ((truncation 2).map
    ((ihom (Δ[n] : SSet.{u})).map ((ihom P).map q.hom)))
  let B₀ := (functorEdgeOfSimplicialHomotopy r.boundaryFractionHomotopy).map
    ((truncation 2).map ((pre (joinStdSimplexIso 0 0).hom).app ((ihom P).obj C.obj)))
  have hFp : joinInl (Δ[n] : SSet.{u}) Δ[0] ≫ F =
      internalHomFlipHomEquiv P Δ[n] B.obj
        (r.cylinder.homotopy.h ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj) ≫
        (ihom P).map q.hom := by
    dsimp only [F]
    rw [← internalHomFlipHomEquiv_pre_app, Category.assoc,
      (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).naturality q.hom, ← Category.assoc]
    exact spanInternalHomFlip_post q.hom _
  have hTp : joinInl (Δ[n] : SSet.{u}) Δ[0] ≫ T =
      (D ≫ q.hom) ≫ constantFunctorMap P C.obj := by
    dsimp only [T]
    rw [← internalHomFlipHomEquiv_pre_app, Category.assoc, U.fixedPrefix,
      SSet.comp_const, spanInternalHomFlip_const]
    rfl
  have hAs : ((ihom (Δ[n] : SSet.{u})).map ((ihom P).map q.hom)).app
      (Opposite.op ⦋0⦌) (squareVertex r.cylinderSquare 0 0) =
      functorVertex (joinInl (Δ[n] : SSet.{u}) Δ[0] ≫ F) := by
    rw [r.cylinderSquare_source]
    change functorVertex
      (internalHomFlipHomEquiv P Δ[n] B.obj
        (r.cylinder.homotopy.h ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj) ≫
        (ihom P).map q.hom) = _
    rw [hFp]
  have hAt : ((ihom (Δ[n] : SSet.{u})).map ((ihom P).map q.hom)).app
      (Opposite.op ⦋0⦌) (squareVertex r.cylinderSquare 0 1) =
      functorVertex (joinInl (Δ[n] : SSet.{u}) Δ[0] ≫ T) := by
    rw [r.cylinderSquare_original]
    change functorVertex ((D ≫ constantFunctorMap P B.obj) ≫ (ihom P).map q.hom) = _
    have hc := spanInternalHomFlip_post q.hom
      (SSet.const (functorVertex D) : P ⟶ (ihom (Δ[n] : SSet.{u})).obj B.obj)
    have hmap : ((ihom (Δ[n] : SSet.{u})).map q.hom).app (Opposite.op ⦋0⦌)
        (functorVertex D) = functorVertex (D ≫ q.hom) := rfl
    rw [SSet.const_comp, hmap, spanInternalHomFlip_const, spanInternalHomFlip_const] at hc
    rw [hTp]
    exact congrArg functorVertex hc.symm
  let A' := (SSet.Edge.ofTruncated A₀).ofEq hAs hAt
  let V := r.boundary.h ≫ verdierSpanEvaluationSquare h
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z
  have hFn : r.cylinder.homotopy.h ≫ (ihom J).map q.hom ≫
      (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app C.obj =
      (V ≫ (pre squareBottomEdge).app C.obj) ≫ (pre (joinStdSimplexIso 0 0).hom).app C.obj := by
    rw [(pre (joinMap (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).naturality q.hom,
      ← Category.assoc, r.cylinder.homotopy_next]
    dsimp only [V]
    simp only [Category.assoc]
    have he := congrArg (fun g => r.boundary.h ≫ g ≫
      (pre (joinStdSimplexIso 0 0).hom).app C.obj)
      (verdierSpanEvaluationSquare_bottom h
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z)
    simp only [Category.assoc] at he
    rw [he]
    simp only [verdierSpanFamilyNumeratorArrow, Category.assoc]
    rw [(pre (joinStdSimplexIso 0 0).hom).naturality q.hom]
  have hTn : ((S.ι ▷ Δ[1]) ≫ U.whole) ≫
      (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app C.obj =
      (V ≫ (pre squareTopEdge).app C.obj) ≫ (pre (joinStdSimplexIso 0 0).hom).app C.obj := by
    dsimp only [V]
    simp only [Category.assoc]
    have he := congrArg (fun g => r.boundary.h ≫ g ≫
      (pre (joinStdSimplexIso 0 0).hom).app C.obj)
      (verdierSpanEvaluationSquare_top h
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z)
    simp only [Category.assoc] at he
    rw [he]
    simpa only [Category.assoc] using U.boundary_next
  have hFB : joinMap (simplexLastPoint n) (𝟙 Δ[0]) ≫ F =
      (joinStdSimplexIso 0 0).hom ≫
        internalHomFlipHomEquiv P Δ[1] C.obj (V ≫ (pre squareBottomEdge).app C.obj) := by
    dsimp only [F]
    rw [← internalHomFlipHomEquiv_pre_app, Category.assoc, hFn,
      internalHomFlipHomEquiv_pre_app]
  have hTB : joinMap (simplexLastPoint n) (𝟙 Δ[0]) ≫ T =
      (joinStdSimplexIso 0 0).hom ≫
        internalHomFlipHomEquiv P Δ[1] C.obj (V ≫ (pre squareTopEdge).app C.obj) := by
    dsimp only [T]
    rw [← internalHomFlipHomEquiv_pre_app, hTn, internalHomFlipHomEquiv_pre_app]
  have hBs : functorVertex ((joinStdSimplexIso 0 0).hom ≫
      internalHomFlipHomEquiv P Δ[1] C.obj (V ≫ (pre squareBottomEdge).app C.obj)) =
      functorVertex (joinMap (simplexLastPoint n) (𝟙 Δ[0]) ≫ F) := by
    rw [hFB]
  have hBt : functorVertex ((joinStdSimplexIso 0 0).hom ≫
      internalHomFlipHomEquiv P Δ[1] C.obj (V ≫ (pre squareTopEdge).app C.obj)) =
      functorVertex (joinMap (simplexLastPoint n) (𝟙 Δ[0]) ≫ T) := by
    rw [hTB]
  let B' := (SSet.Edge.ofTruncated B₀).ofEq hBs hBt
  have hab : SSet.yonedaEquiv.symm A'.edge ≫
      (pre (simplexLastPoint n)).app ((ihom P).obj C.obj) =
      SSet.yonedaEquiv.symm B'.edge ≫
        (pre (joinInl (Δ[0] : SSet.{u}) Δ[0])).app ((ihom P).obj C.obj) := by
    change SSet.yonedaEquiv.symm A₀.edge ≫
      (pre (simplexLastPoint n)).app ((ihom P).obj C.obj) =
      SSet.yonedaEquiv.symm (((pre (joinStdSimplexIso 0 0).hom).app ((ihom P).obj C.obj)).app
        (Opposite.op ⦋1⦌) (functorEdgeOfSimplicialHomotopy r.boundaryFractionHomotopy).edge) ≫
        (pre (joinInl (Δ[0] : SSet.{u}) Δ[0])).app ((ihom P).obj C.obj)
    rw [← SSet.yonedaEquiv_symm_comp, Category.assoc, ← NatTrans.comp_app,
      ← pre_map, joinStdSimplexIso_zero_inl]
    exact r.boundaryFractionComparison_sharedSource.symm
  obtain ⟨l, hlp, hln⟩ := exists_simplexAttachmentComparison n F T A'.toTruncated
    B'.toTruncated hab
  have hai : IsInvertibleEdge (X := (ihom (Δ[n] : SSet.{u})).obj ((ihom P).obj C.obj))
      A'.toTruncated :=
    (isInvertibleEdge_congr (e := A₀) (f := A'.toTruncated) rfl).mp
      r.cylinderSquare_left_quotient_isInvertible
  have hbi : IsInvertibleEdge
      (X := (ihom (join (Δ[0] : SSet.{u}) Δ[0])).obj ((ihom P).obj C.obj)) B'.toTruncated :=
    (isInvertibleEdge_congr (e := B₀) (f := B'.toTruncated) rfl).mp
      (r.boundaryFractionComparison_isInvertible.map
        ((pre (joinStdSimplexIso 0 0).hom).app ((ihom P).obj C.obj)))
  have hli := simplexAttachmentComparison_isInvertible n l
    ((isInvertibleEdge_congr hlp).mpr hai) ((isInvertibleEdge_congr hln).mpr hbi)
  exact ⟨⟨l, hli, hlp, hln⟩⟩

def VerdierRecoveredBoundaryComparison.iso
    {r : VerdierFiniteMappingCoconeRecovery h D z S a f}
    {U : VerdierRecoveredQuotientCoconeCylinder r G}
    (c : VerdierRecoveredBoundaryComparison r U) :
    FunctorIso (r.cylinder.homotopy.h ≫ (ihom J).map q.hom) ((S.ι ▷ Δ[1]) ≫ U.whole) := by
  have := c.isInvertible
  exact spanFunctorIsoUnflip (asIso (Truncated.HomotopyCategory.homMk c.edge))

namespace VerdierRecoveredBoundaryComparison
open SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison
variable {r : VerdierFiniteMappingCoconeRecovery h D z S a f}
  {U : VerdierRecoveredQuotientCoconeCylinder r G}
  (c : VerdierRecoveredBoundaryComparison r U)

lemma target_inverts (_c : VerdierRecoveredBoundaryComparison r U) :
    InvertsEdges ((S.ι ▷ Δ[1]) ≫ U.whole) Set.univ := by
  have hc := (invertsAllEdges_toKan ((S.ι ▷ Δ[1]) ≫ U.coreWhole)).comp
    (quasicategoryCore ((ihom J).obj C.obj)).ι
  simpa only [Category.assoc, U.coreWhole_ι] using hc

/-- 同じ全比較辺を、元の実 core 円柱と商 core 円柱の間の同じ全 prism に戻す。 -/
def coreHomotopy : SSet.Homotopy
    (r.relativeCylinder ≫ relativeFunctorCoreQuotient q.hom J)
    ((S.ι ▷ Δ[1]) ≫ U.coreWhole) := by
  let H := spanFunctorEdgeUnflipCoreHomotopy c.edge c.isInvertible c.target_inverts
  have hF : r.relativeCylinder ≫ relativeFunctorCoreQuotient q.hom J =
      allEdgesCoreLift (r.cylinder.homotopy.h ≫ (ihom J).map q.hom)
        (spanFunctorEdgeUnflip_invertsAllEdges c.edge c.isInvertible c.target_inverts) := rfl
  have hG : allEdgesCoreLift ((S.ι ▷ Δ[1]) ≫ U.whole) c.target_inverts =
      (S.ι ▷ Δ[1]) ≫ U.coreWhole := by
    apply (cancel_mono (quasicategoryCore ((ihom J).obj C.obj)).ι).mp
    rw [allEdgesCoreLift_ι, Category.assoc, U.coreWhole_ι]
  exact { h := H.h, h₀ := H.h₀.trans hF.symm, h₁ := H.h₁.trans hG, rel := H.rel }

lemma coreHomotopy_ι : c.coreHomotopy.h ≫ (quasicategoryCore ((ihom J).obj C.obj)).ι =
    uncurry (SSet.yonedaEquiv.symm c.edge.edge ≫ (internalHomSwapIso J P C.obj).hom) :=
  spanFunctorEdgeUnflipCoreHomotopy_ι c.edge c.isInvertible c.target_inverts

/-- 元の第一行商を始端とする全境界比較。円柱の二胞体と指定比較辺を選び直さない。 -/
def simplexQuotientHomotopy : SSet.Homotopy
    (r.simplexCylinder ≫ relativeFirstRowSimplexQuotient q (n + 1))
    (((S.ι ▷ Δ[1]) ≫ U.coreWhole) ≫
      quasicategoryCoreMap ((pre (joinStdSimplexIso n 0).inv).app C.obj)) := by
  let H := functorHomotopyPostcomp c.coreHomotopy
    (quasicategoryCoreMap ((pre (joinStdSimplexIso n 0).inv).app C.obj))
  have hs : (r.relativeCylinder ≫ relativeFunctorCoreQuotient q.hom J) ≫
      quasicategoryCoreMap ((pre (joinStdSimplexIso n 0).inv).app C.obj) =
      r.simplexCylinder ≫ relativeFirstRowSimplexQuotient q (n + 1) := by
    apply (cancel_mono (quasicategoryCore ((ihom (Δ[n + 1] : SSet.{u})).obj C.obj)).ι).mp
    rw [Category.assoc, quasicategoryCoreMap_ι]
    rfl
  exact { h := H.h, h₀ := H.h₀.trans hs, h₁ := H.h₁, rel := H.rel }

lemma simplexQuotientHomotopy_ι : c.simplexQuotientHomotopy.h ≫
    (quasicategoryCore ((ihom (Δ[n + 1] : SSet.{u})).obj C.obj)).ι =
    uncurry (SSet.yonedaEquiv.symm c.edge.edge ≫ (internalHomSwapIso J P C.obj).hom) ≫
      (pre (joinStdSimplexIso n 0).inv).app C.obj := by
  change (c.coreHomotopy.h ≫
    quasicategoryCoreMap ((pre (joinStdSimplexIso n 0).inv).app C.obj)) ≫ _ = _
  rw [Category.assoc, quasicategoryCoreMap_ι, ← Category.assoc, c.coreHomotopy_ι]

/-- 元の亜群化比較上の、構成済み境界二胞体から得られる同じ全関手同型。 -/
def completionComparisonIso : FunctorIso
    ((r.simplexCylinder ≫ groupoidCompletionMap
      (relativeFirstRowSimplex q (n + 1) : SSet.{u})) ≫
      relativeFirstRowSimplexCompletionComparison q (n + 1))
    (((S.ι ▷ Δ[1]) ≫ U.coreWhole) ≫
      quasicategoryCoreMap ((pre (joinStdSimplexIso n 0).inv).app C.obj)) := by
  have e := FunctorIso.precomp
    (relativeFirstRowSimplexCompletionComparison_unitIso q (n + 1)) r.simplexCylinder
  exact e ≪≫ functorIsoOfSimplicialHomotopy c.simplexQuotientHomotopy

end VerdierRecoveredBoundaryComparison

/-- 元の有限商余錐族と実境界から、同じ両円柱と指定二胞体を保つ全境界比較を一括回収する。 -/
lemma exists_verdierFiniteCoconeBoundaryRecovery [K.Finite] [S.toSSet.Finite]
    (G : K ⟶ (ihom J).obj C.obj)
    (hG : G ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj =
      SSet.const (functorVertex (D ≫ q.hom)))
    (hz : G ≫ evaluateFunctorAt ((joinInr (Δ[n] : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) = SSet.const (q.hom.app (Opposite.op ⦋0⦌) z))
    (ha : a ≫ verdierDenominatorSpanCanonicalComparison i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z ≫
      fixedFractionEvaluation q.hom (weakEquivalences i) h.inverts
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z =
      S.ι ≫ spanCoconeLastMapping (D ≫ q.hom) (q.hom.app (Opposite.op ⦋0⦌) z) G hG hz) :
    ∃ r : VerdierFiniteMappingCoconeRecovery h D z S a
        (spanCoconeLastMapping (D ≫ q.hom) (q.hom.app (Opposite.op ⦋0⦌) z) G hG hz),
      ∃ U : VerdierRecoveredQuotientCoconeCylinder r G,
        Nonempty (VerdierRecoveredBoundaryComparison r U) := by
  let fG := spanCoconeLastMapping (D ≫ q.hom) (q.hom.app (Opposite.op ⦋0⦌) z) G hG hz
  obtain ⟨r⟩ := exists_verdierFiniteMappingCoconeRecovery h D z S a fG ha
  have hGe := spanCoconeLastMapping_edge (D ≫ q.hom) (q.hom.app (Opposite.op ⦋0⦌) z) G hG hz
  obtain ⟨U⟩ := exists_verdierRecoveredQuotientCoconeCylinder r G hG hGe
  exact ⟨r, U, exists_verdierRecoveredBoundaryComparison r U⟩

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exists_verdierFiniteCoconeBoundaryRecovery := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.exists_verdierFiniteCoconeBoundaryRecovery

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exists_verdierRecoveredBoundaryComparison := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.exists_verdierRecoveredBoundaryComparison

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.casesOn := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.completionComparisonIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.completionComparisonIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.completionComparisonIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.coreHomotopy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.coreHomotopy := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.coreHomotopy

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.coreHomotopy_ι := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.coreHomotopy_ι

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.ctorIdx := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.edge (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.edge := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.edge

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.isInvertible := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.isInvertible

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.iso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.iso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.iso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.last_eq := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.last_eq

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.mk := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.noConfusion := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.noConfusionType := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.noConfusionType

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.prefix_eq := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.prefix_eq

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.rec := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.recOn := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.simplexQuotientHomotopy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.simplexQuotientHomotopy := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.simplexQuotientHomotopy

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.simplexQuotientHomotopy_ι := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.simplexQuotientHomotopy_ι

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.target_inverts := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.target_inverts

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.completionComparisonIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.completionComparisonIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.coreHomotopy._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.coreHomotopy._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.coreHomotopy._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.coreHomotopy._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.coreHomotopy._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.coreHomotopy._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.coreHomotopy._proof_4 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.coreHomotopy._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.coreHomotopy._proof_5 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.coreHomotopy._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.coreHomotopy._proof_6 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.coreHomotopy._proof_6

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.mk.inj := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.mk.injEq := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.mk.sizeOf_spec

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.simplexQuotientHomotopy._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.simplexQuotientHomotopy._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.simplexQuotientHomotopy._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.simplexQuotientHomotopy._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.simplexQuotientHomotopy._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.simplexQuotientHomotopy._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.simplexQuotientHomotopy._proof_4 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison.simplexQuotientHomotopy._proof_4
