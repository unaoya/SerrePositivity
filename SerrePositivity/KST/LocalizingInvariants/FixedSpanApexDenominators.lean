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
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) (W : Set (X _⦋1⦌)) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F W ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges G W := by
  constructor
  · intro h s hs
    exact (NatIso.isIso_map_iff e.toNatIso
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s))).mp (h hs)
  · intro h s hs
    exact (NatIso.isIso_map_iff e.toNatIso
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s))).mpr (h hs)

lemma invertsEdges_const (X Q : SSet.{u}) (q : Q _⦋0⦌) (W : Set (X _⦋1⦌)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (SSet.const q : X ⟶ Q) W := by
  intro s _
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isEquivalencePathVertex_const q
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex at h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_functorVertex] at h
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s).map ((truncation 2).map (SSet.const q : X ⟶ Q)))
    (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant q 1)) rfl).mpr h

lemma fixedMarkedSpanApexImage_inverts {X Q : SSet.{u}} [Quasicategory Q] (F : X ⟶ Q)
    (W : Set (X _⦋1⦌)) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F W) (x y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (fixedMarkedSpanApex X W x y ≫ F) Set.univ :=
  (invertsEdges_functorIso_iff (fixedMarkedSpanApexImageIso F W hF x y) Set.univ).mpr
    (invertsEdges_const _ _ _ Set.univ)

lemma fixedMarkedSpanApex_edges_mem {X Q : SSet.{u}} [Quasicategory Q] (F : X ⟶ Q)
    (W : Set (X _⦋1⦌)) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F W) (hW : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges F = W)
    (x y : X _⦋0⦌) (s : (fixedMarkedSpans X W x y) _⦋1⦌) :
    (fixedMarkedSpanApex X W x y).app (Opposite.op ⦋1⦌) s ∈ W := by
  apply hW.subset
  have h := fixedMarkedSpanApexImage_inverts F W hF x y (a := s) (Set.mem_univ s)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s).map ((truncation 2).map (fixedMarkedSpanApex X W x y ≫ F)))
    (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((fixedMarkedSpanApex X W x y).app (Opposite.op ⦋1⦌) s)).map
      ((truncation 2).map F)) rfl).mp h

lemma tammeFixedMarkedSpanApex_edges_mem {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E) (x y : (laxCategory p q).obj _⦋0⦌)
    (s : (fixedMarkedSpans (laxCategory p q).obj (tammeLocalizingEdges p q) x y) _⦋1⦌) :
    (fixedMarkedSpanApex (laxCategory p q).obj (tammeLocalizingEdges p q) x y).app
      (Opposite.op ⦋1⦌) s ∈ tammeLocalizingEdges p q :=
  fixedMarkedSpanApex_edges_mem (tammeQuotientMap p q) (tammeLocalizingEdges p q)
    (tammeQuotient_isLocalization p q).choose (tammeQuotientMap_invertedEdges p q) x y s

end SerrePositivity.KST.LocalizingInvariants
