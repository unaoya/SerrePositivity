module

public import SerrePositivity.KST.LocalizingInvariants.FixedSpanApexComparison
public import SerrePositivity.KST.LocalizingInvariants.TammeQuotientDetection

/-!
概要：両端固定 span の全ての射の頂点成分は、元の Tamme 分母である。
方針：頂点の像の関手を定値関手と自然同型にし、全ての辺の反転を元の辺集合へ戻す。
規約：h 圏の形式的な分母だけでなく、元の一単体の分母性。
使われ方：分数 span の refinement を全て反転する亜群化の解析。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma invertsEdges_functorIso_iff {X Q : SSet.{u}} {F G : X ⟶ Q}
    (e : FunctorIso F G) (W : Set (X _⦋1⦌)) : InvertsEdges F W ↔ InvertsEdges G W := by
  constructor
  · intro h s hs
    exact (NatIso.isIso_map_iff e.toNatIso
      (SSet.Truncated.HomotopyCategory.homMk (edgeOfSimplex s))).mp (h hs)
  · intro h s hs
    exact (NatIso.isIso_map_iff e.toNatIso
      (SSet.Truncated.HomotopyCategory.homMk (edgeOfSimplex s))).mpr (h hs)

lemma invertsEdges_const (X Q : SSet.{u}) (q : Q _⦋0⦌) (W : Set (X _⦋1⦌)) :
    InvertsEdges (SSet.const q : X ⟶ Q) W := by
  intro s _
  have h := isEquivalencePathVertex_const q
  unfold IsEquivalencePathVertex at h
  rw [intervalFunctorVertexEdge_functorVertex] at h
  exact (isInvertibleEdge_congr
    (e := (edgeOfSimplex s).map ((truncation 2).map (SSet.const q : X ⟶ Q)))
    (f := edgeOfSimplex (PinchedHom.constant q 1)) rfl).mpr h

lemma fixedMarkedSpanApexImage_inverts {X Q : SSet.{u}} [Quasicategory Q] (F : X ⟶ Q)
    (W : Set (X _⦋1⦌)) (hF : InvertsEdges F W) (x y : X _⦋0⦌) :
    InvertsEdges (fixedMarkedSpanApex X W x y ≫ F) Set.univ :=
  (invertsEdges_functorIso_iff (fixedMarkedSpanApexImageIso F W hF x y) Set.univ).mpr
    (invertsEdges_const _ _ _ Set.univ)

lemma fixedMarkedSpanApex_edges_mem {X Q : SSet.{u}} [Quasicategory Q] (F : X ⟶ Q)
    (W : Set (X _⦋1⦌)) (hF : InvertsEdges F W) (hW : invertedEdges F = W)
    (x y : X _⦋0⦌) (s : (fixedMarkedSpans X W x y) _⦋1⦌) :
    (fixedMarkedSpanApex X W x y).app (Opposite.op ⦋1⦌) s ∈ W := by
  apply hW.subset
  have h := fixedMarkedSpanApexImage_inverts F W hF x y (a := s) (Set.mem_univ s)
  exact (isInvertibleEdge_congr
    (e := (edgeOfSimplex s).map ((truncation 2).map (fixedMarkedSpanApex X W x y ≫ F)))
    (f := (edgeOfSimplex ((fixedMarkedSpanApex X W x y).app (Opposite.op ⦋1⦌) s)).map
      ((truncation 2).map F)) rfl).mp h

lemma tammeFixedMarkedSpanApex_edges_mem {C D E : StableCategory.{u}}
    (p : ExactMap C E) (q : ExactMap D E) (x y : (laxCategory p q).obj _⦋0⦌)
    (s : (fixedMarkedSpans (laxCategory p q).obj (tammeLocalizingEdges p q) x y) _⦋1⦌) :
    (fixedMarkedSpanApex (laxCategory p q).obj (tammeLocalizingEdges p q) x y).app
      (Opposite.op ⦋1⦌) s ∈ tammeLocalizingEdges p q :=
  fixedMarkedSpanApex_edges_mem (tammeQuotientMap p q) (tammeLocalizingEdges p q)
    (tammeQuotient_isLocalization p q).choose (tammeQuotientMap_invertedEdges p q) x y s

end SerrePositivity.KST.LocalizingInvariants
