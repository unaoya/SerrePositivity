module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagrams
public import SerrePositivity.InfinityCategories.F1.Coherent.EnrichedHomotopy
public import SerrePositivity.InfinityCategories.Core.FullSubcomplexEdgeLift
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FullSubcomplexMapping
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise

/-!
概要：完全関手の関手同型を StableInfinity の同じ射の類へ移す。
方針：可逆辺を完全関手の全部分複体へ持ち上げ、その core 内の同型を使う。
規約：安定対象と元の完全関手の端点を保持する。使われ方：Verdier 四角形の実現。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Stable.Exact
open SerrePositivity.KST.LocalizingInvariants

/-- core による豊穣移送の頂点は元の完全関手の頂点を保つ。 -/
lemma stableHomVertex_val {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B) :
    (SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableQCat.{u}) A B F).val =
      _root_.SerrePositivity.InfinityCategories.Stable.Verdier.exactFunctorVertexEquiv A B F := by
  apply Subtype.ext
  simp only [SimplicialCategory.homEquiv', Equiv.trans_apply]
  rfl

/-- 完全関手の関手同型は、core を取った実際の豊穣 Hom の頂点同型になる。 -/
def exactMapCoreVertexIso {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {F G : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B}
    (h : FunctorIso F.hom G.hom) :
    VertexIso (SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableQCat.{u}) A B F)
      (SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableQCat.{u}) A B G) := by
  let a := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.exactFunctorVertexEquiv A B F
  let b := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.exactFunctorVertexEquiv A B G
  let l := Classical.choose
    (exists_fullSubcomplexEdgeLift (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsExactVertex A B) a b (FunctorIso.edge h))
  have hl := Classical.choose_spec
    (exists_fullSubcomplexEdgeLift (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsExactVertex A B) a b (FunctorIso.edge h))
  have hi : IsInvertibleEdge l := by
    apply (isFullyFaithful_fullSubcomplexOnVertices_ι _ _).reflects_isInvertibleEdge l
    rw [hl]
    exact FunctorIso.edge_isInvertible h
  let e : SSet.Edge (X := SimplicialCategory.sHom (C := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableQCat.{u}) A B)
      (SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableQCat.{u}) A B F)
      (SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableQCat.{u}) A B G) := {
    edge := ⟨l.edge, (quasicategoryCore_mem_edge_iff _).2
      ((isInvertibleEdge_congr (by rfl)).2 hi)⟩
    src_eq := by
      apply Subtype.ext
      exact l.src_eq.trans (_root_.SerrePositivity.InfinityCategories.Stable.Exact.stableHomVertex_val F).symm
    tgt_eq := by
      apply Subtype.ext
      exact l.tgt_eq.trans (_root_.SerrePositivity.InfinityCategories.Stable.Exact.stableHomVertex_val G).symm }
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk e.toTruncated) :=
    IsGroupoid.all_isIso (C := hoFunctor.obj (SimplicialCategory.sHom
      (C := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableQCat.{u}) A B)) _
  exact asIso (SSet.Truncated.HomotopyCategory.homMk e.toTruncated)

/-- 関手同型で結ばれた完全関手は StableInfinity の同じ射を表す。 -/
lemma stableArrow_homMk_eq_of_functorIso {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}}
    {F G : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} (h : FunctorIso F.hom G.hom) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow F).toTruncated =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow G).toTruncated :=
  coherentNerveEdge_homMk_eq_of_enrichedVertexIso (C := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableQCat.{u})
    (_root_.SerrePositivity.InfinityCategories.Stable.Exact.exactMapCoreVertexIso h)

end SerrePositivity.InfinityCategories.Stable.Exact

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Exact.exactMapCoreVertexIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactMapCoreVertexIso := _root_.SerrePositivity.InfinityCategories.Stable.Exact.exactMapCoreVertexIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableArrow_homMk_eq_of_functorIso := _root_.SerrePositivity.InfinityCategories.Stable.Exact.stableArrow_homMk_eq_of_functorIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableHomVertex_val := _root_.SerrePositivity.InfinityCategories.Stable.Exact.stableHomVertex_val

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactMapCoreVertexIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.exactMapCoreVertexIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactMapCoreVertexIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.exactMapCoreVertexIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactMapCoreVertexIso._proof_3 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.exactMapCoreVertexIso._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactMapCoreVertexIso._proof_4 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.exactMapCoreVertexIso._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactMapCoreVertexIso._proof_5 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.exactMapCoreVertexIso._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactMapCoreVertexIso._proof_6 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.exactMapCoreVertexIso._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactMapCoreVertexIso._proof_7 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.exactMapCoreVertexIso._proof_7

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactMapCoreVertexIso._proof_8 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.exactMapCoreVertexIso._proof_8

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactMapCoreVertexIso._proof_9 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.exactMapCoreVertexIso._proof_9
