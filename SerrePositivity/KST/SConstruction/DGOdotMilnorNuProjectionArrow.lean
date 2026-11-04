module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuSquareBoundary
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulIso
public import SerrePositivity.KST.SConstruction.CoherentHomIntervalEdgeParameter
public import SerrePositivity.InfinityCategories.Stable.Exact.ExactMapHomotopy

/-!
概要：同じ実商辺の指定関手同型を、StableInfinity の辺全体の比較へ移す。
方針：指定した豊穣 Hom の辺を標準区間比較へ写し、固定端点の内部 Hom で読む。
規約：商境界の比較であり、零角を含む全四角形比較の存在とは区別する。
使われ方：実面の VerdierSquareDiagramIso に指定する商境界の具体的入力。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalClosed SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : DGGluingMilnorSquare R d)
local instance : IsDGPretriangulated R (DGOdotGluing R d) :=
  dgGluingMilnor_isDGPretriangulated R d
local notation "A" => dgKInputStableValue R (dgOdotMilnorCellInput R d)
local notation "B" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)
local notation "F" => dgOdotMilnorCellProjectionExactMap R d
local notation "G" => PerfectVerdierSequence.projection (dgOdotMilnorNuPerfectSequence R d h)
local instance : KanComplex
    (SimplicialCategory.sHom (C := StableQCat.{u + 1}) (A) (B)) :=
  stableQCat_sHom_kanComplex (A) (B)

/-- 概要：同じ指定商比較の豊穣 Hom 内の実辺。
方針：構成済み関手同型の core 像の順方向を実辺で表示する。
規約：元の二つの完全射を固定する。使われ方：標準区間比較のパラメータ。 -/
def dgOdotMilnorNuProjectionCoreEdge :
    (SimplicialCategory.sHom (C := StableQCat.{u + 1}) (A) (B)).Edge
      (SimplicialCategory.homEquiv' (C := StableQCat.{u + 1}) (A) (B) (F))
      (SimplicialCategory.homEquiv' (C := StableQCat.{u + 1}) (A) (B) (G)) :=
  Edge.ofTruncated (homotopyCategory_homMk_surjective _ _
    (exactMapCoreVertexIso (dgOdotMilnorNuPerfectProjectionComparison R d h)).hom).choose

/-- 概要：元の実商辺と完備化後射影の辺は、端点固定の関手全体として同型。
方針：元 Hom 辺の可逆性を宇宙持ち上げ・標準区間比較・fiber 包含で保つ。
規約：同じ辺の代表を保持し、全四角形比較はまだ結論しない。
使われ方：Sp の指定商境界の全一単体比較。 -/
def dgOdotMilnorNuProjectionArrowComparison : FunctorIso
    (SSet.yonedaEquiv.symm (stableArrow (F)).edge)
    (SSet.yonedaEquiv.symm (stableArrow (G)).edge) := by
  let e := dgOdotMilnorNuProjectionCoreEdge R d h
  have hi : IsInvertibleEdge e.toTruncated :=
    IsGroupoid.all_isIso (C := hoFunctor.obj
      (SimplicialCategory.sHom (C := StableQCat.{u + 1}) (A) (B))) _
  let a := coherentHomIntervalEdgeFromParameter (C := StableQCat.{u + 1}) (F) (G) e
  have ha : IsInvertibleEdge a.toTruncated := by
    have hh := hi.ulift.map (coherentHomIntervalComparison (C := StableQCat.{u + 1}) (A) (B))
    exact (isInvertibleEdge_congr (by rfl)).mp hh
  let b := a.map (vertexFiberι ((pre (boundary 1).ι).app StableInfinity.{u + 1})
    (functorVertex (intervalMappingBoundary (coherentNerveVertex (A))
      (coherentNerveVertex (B)))))
  exact @asIso _ _ _ _ (Truncated.HomotopyCategory.homMk b.toTruncated) (ha.map _)

/-- 概要：同じ端点固定の商辺比較を元の Cat^perf の全辺へ戻す。
方針：充満忠実な Cat^perf 包含で構成済みの全比較を反映する。
規約：比較する完全射と両頂点の完備性証拠は同じ。使われ方：指定商境界。 -/
def dgOdotMilnorNuPerfectProjectionArrowComparison : FunctorIso
    (SSet.yonedaEquiv.symm (perfectStableArrow (F)
      (dgKInputStableValue_isIdempotentComplete R (dgOdotMilnorCellInput R d))
      (dgKInputStableValue_isIdempotentComplete R (dgOdotMilnorResolvedInput R d))).edge)
    (SSet.yonedaEquiv.symm (perfectStableArrow (G)
      (dgOdotMilnorNuPerfectSequence R d h).middle_complete
      (dgOdotMilnorNuPerfectSequence R d h).right_complete).edge) := by
  apply perfectStableInfinityInclusion_isFullyFaithful.preimageFunctorIso
  rw [perfectStableArrow_inclusion, perfectStableArrow_inclusion]
  exact dgOdotMilnorNuProjectionArrowComparison R d h

/-- 概要：絶対核列の包含辺と同じ実 ν 面の包含辺を全一単体で比較する。
方針：元の同じ包含辺の厳密回収を使用する。
規約：境界比較だけで全四角形比較を結論しない。使われ方：指定包含境界。 -/
def dgOdotMilnorNuNullSquareInclusionBoundary : FunctorIso
    (squareBottomEdge ≫ (dgOdotMilnorNuPerfectSequence R d h).presentation.square)
    (squareBottomEdge ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R) := by
  rw [PerfectVerdierSequence.presentation_bottom,
    dgOdotMilnorPerfectNullSquare_nu_inclusion R d h]

/-- 概要：絶対核列の商辺と同じ実 ν 面の商辺を全一単体の関手同型で比較する。
方針：元の実右辺回収と端点固定の同じ商辺比較を合成する。
規約：零角を含む全四角形比較は別途必要。使われ方：指定商境界。 -/
def dgOdotMilnorNuNullSquareProjectionBoundary : FunctorIso
    (squareRightEdge ≫ (dgOdotMilnorNuPerfectSequence R d h).presentation.square)
    (squareRightEdge ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R) := by
  rw [PerfectVerdierSequence.presentation_right,
    dgOdotMilnorPerfectNullSquare_nu_projection R d]
  exact (dgOdotMilnorNuPerfectProjectionArrowComparison R d h).symm

end SerrePositivity.KST.SConstruction
