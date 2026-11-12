module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullDiagonalMaps
public import SerrePositivity.KST.SConstruction.CoherentHomIntervalEdgeParameter

/-!
概要：同じ共有対角の零 Hom 比較を元一単体全体の同じ関手同型へ移す。
方針：元の比較辺を固定端点の標準 coherent 区間比較へ写す。
規約：元共有対角・元比較辺を変更しない。使われ方：上下二胞体比較の共通全辺。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalClosed SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)
local notation "K" => dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d)
local notation "B" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)
local notation "F" => dgOdotMilnorNuNullDiagonalMap R d
local notation "G" => dgOdotMilnorNuAbsoluteDiagonalMap R d h

local instance nuNullDiagonalHom_kanComplex :
    KanComplex (SimplicialCategory.sHom (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (K) (B)) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableQCat_sHom_kanComplex (K) (B)

/-- 概要：同じ共有対角比較の始点は元実対角完全射の Hom 頂点。
方針：元全因子分解の回収と元対角完全射の頂点式を合成する。
規約：同じ元頂点。使われ方：固定端点の全辺比較。 -/
lemma dgOdotMilnorNuNullDiagonalComparison_source :
    (dgOdotMilnorNuNullCoherenceHom R d h).app (Opposite.op ⦋0⦌)
      (dgOdotMilnorNuNullDiagonalVertex R d) =
      SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (K) (B) (F) := by
  have he := ConcreteCategory.congr_hom
    (NatTrans.congr_app (dgOdotMilnorNuNullTriangleFactor_hom R d h 0) (Opposite.op ⦋0⦌))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullDiagonalPath.{u})
  exact he.trans (dgOdotMilnorNuNullDiagonalMap_vertex R d)

/-- 概要：同じ共有対角比較の終点は元絶対対角完全射の Hom 頂点。
方針：元絶対全因子分解の回収と元対角頂点式を合成する。
規約：同じ元頂点。使われ方：同じ固定端点比較の終点。 -/
lemma dgOdotMilnorNuNullDiagonalComparison_target :
    (dgOdotMilnorNuNullCoherenceHom R d h).app (Opposite.op ⦋0⦌)
      (dgOdotMilnorNuAbsoluteDiagonalVertex R d h) =
      SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (K) (B) (G) := by
  have he := ConcreteCategory.congr_hom
    (NatTrans.congr_app (dgOdotMilnorNuAbsoluteTriangleFactor_hom R d h 0) (Opposite.op ⦋0⦌))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullDiagonalPath.{u})
  exact he.trans (dgOdotMilnorNuAbsoluteDiagonalMap_vertex R d h)

/-- 概要：同じ共有対角比較を元完全射を端点とする実豊穣 Hom 辺へ移す。
方針：同じ零 Hom 包含で元の辺を写し、同じ端点回収式を使う。
規約：元比較辺を選び直さない。使われ方：標準 coherent 全辺比較の入力。 -/
def dgOdotMilnorNuNullDiagonalCoreEdge :
    (SimplicialCategory.sHom (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (K) (B)).Edge
      (SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (K) (B) (F))
      (SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (K) (B) (G)) :=
  ((dgOdotMilnorNuNullDiagonalComparisonEdge R d h).map
    (dgOdotMilnorNuNullCoherenceHom R d h)).ofEq
      (dgOdotMilnorNuNullDiagonalComparison_source R d h)
      (dgOdotMilnorNuNullDiagonalComparison_target R d h)

/-- 概要：豊穣共有対角の辺は同じ零 Hom 比較の全パラメータ像。
方針：同じ辺写像の Yoneda 自然性を使う。
規約：全単体の等号。使われ方：上下正方形の共同比較の保持。 -/
lemma dgOdotMilnorNuNullDiagonalCoreEdge_parameter :
    SSet.yonedaEquiv.symm (dgOdotMilnorNuNullDiagonalCoreEdge R d h).edge =
      SSet.yonedaEquiv.symm (dgOdotMilnorNuNullDiagonalComparisonEdge R d h).edge ≫
        dgOdotMilnorNuNullCoherenceHom R d h :=
  (SSet.yonedaEquiv_symm_comp (X := DGOdotMilnorNuNullCoherenceSpace R d)
    (Y := SimplicialCategory.sHom (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (K) (B))
    (n := ⦋1⦌) (dgOdotMilnorNuNullDiagonalComparisonEdge R d h).edge
      (dgOdotMilnorNuNullCoherenceHom R d h)).symm

/-- 概要：元実／絶対共有対角を元一単体全体の同じ固定端点比較で結ぶ。
方針：同じ豊穣 Hom 辺を標準区間比較と fiber 包含で写す。
規約：元共有対角の全辺を保持。使われ方：上下二胞体を貼る共通関手同型。 -/
def dgOdotMilnorNuNullDiagonalArrowComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (F)).edge)
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (G)).edge) := by
  let e := dgOdotMilnorNuNullDiagonalCoreEdge R d h
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e.toTruncated := IsGroupoid.all_isIso
    (C := hoFunctor.obj (SimplicialCategory.sHom (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (K) (B))) _
  let a := coherentHomIntervalEdgeFromParameter (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (F) (G) e
  have ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge a.toTruncated := by
    have hh := hi.ulift.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (K) (B))
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (by rfl)).mp hh
  let b := a.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((pre (boundary 1).ι).app _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1})
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingBoundary (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (K))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (B)))))
  exact @asIso _ _ _ _ (Truncated.HomotopyCategory.homMk b.toTruncated) (ha.map _)

/-- 概要：同じ共有対角の比較を同じ完備核・商を持つ Cat^perf の全辺へ戻す。
方針：既存の充満忠実包含で同じ実比較を反映する。
規約：同じ元二完全射を保持。使われ方：Sp の全図式比較の共有対角。 -/
def dgOdotMilnorNuNullPerfectDiagonalArrowComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (SSet.yonedaEquiv.symm (perfectStableArrow (F)
      (dgKInputStableValue_isIdempotentComplete R (dgOdotMilnorFlatKernelInput R d))
      (dgKInputStableValue_isIdempotentComplete R (dgOdotMilnorResolvedInput R d))).edge)
    (SSet.yonedaEquiv.symm (perfectStableArrow (G)
      (dgKInputStableValue_isIdempotentComplete R (dgOdotMilnorFlatKernelInput R d))
      (dgKInputStableValue_isIdempotentComplete R (dgOdotMilnorResolvedInput R d))).edge) := by
  apply perfectStableInfinityInclusion_isFullyFaithful.preimageFunctorIso
  rw [perfectStableArrow_inclusion, perfectStableArrow_inclusion]
  exact dgOdotMilnorNuNullDiagonalArrowComparison R d h

end SerrePositivity.KST.SConstruction
