module

public import SerrePositivity.KST.LocalizingInvariants.CorePreimageComparisonPrism
public import SerrePositivity.KST.LocalizingInvariants.VerdierSimplexCoconeLift

/-!
概要：商側の可逆な有限余錐を、元の core 逆像内の実余錐へ精密化する。
方針：実右分数の経路保持比較で全辺反転を反映し、同じ余錐と分母 prism を戻す。
規約：完成分数だけの族に置き換えず、元の余錐・分母・共有経路を保持する。
使われ方：c5 の全図式の亜群化比較における実共通精密化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

/-- 同じ全余錐と分母 prism を、元の core 逆像内でも保持する精密化。 -/
structure VerdierCoreCoconeRefinement {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ B.obj)
    (z : B.obj _⦋0⦌) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (D ≫ q.hom)) where
  source : (Δ[n] : SSet.{u}) ⟶ B.obj
  denominator : Truncated.Edge (X := (truncation 2).obj ((ihom (Δ[n] : SSet.{u})).obj B.obj))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex source) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex D)
  denominator_mem : denominator.edge ∈
    (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌)
  cone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone source
  apex_eq : cone.vertex = z
  source_inverts : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (source ≫ q.hom) Set.univ
  original_inverts : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (D ≫ q.hom) Set.univ
  cone_inverts : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (cone.val ≫ q.hom) Set.univ
  target_inverts : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges d.val Set.univ
  weakCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (corePreimageLift q.hom source source_inverts)
  weakCone_ι : weakCone.val ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).preimage q.hom).ι = cone.val
  weakComparison : SSet.Homotopy (corePreimageLift q.hom source source_inverts)
    (corePreimageLift q.hom D original_inverts)
  weakComparison_ι : weakComparison.h ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).preimage q.hom).ι =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge denominator).h
  comparison : Truncated.Edge
    (X := (truncation 2).obj ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (cone.val ≫ q.hom)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d.val)
  comparison_invertible : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
    (X := (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj) comparison
  comparison_prefix : ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj).app
    (Opposite.op ⦋1⦌) comparison.edge =
      ((ihom (Δ[n] : SSet.{u})).map q.hom).app (Opposite.op ⦋1⦌) denominator.edge
  comparison_apex : SSet.yonedaEquiv.symm comparison.edge ≫
    (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}) Δ[0])).app C.obj =
      curry (snd (Δ[0] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm
        (C.obj.σ 0 (q.hom.app (Opposite.op ⦋0⦌) z)))
  quotientComparison : SSet.Homotopy
    (weakCone.val ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).fromPreimage q.hom)
    (allEdgesCoreLift d.val target_inverts)
  quotientComparison_ι : quotientComparison.h ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).ι =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge comparison).h

/-- 元の Verdier 商の可逆余錐は、全次数で元の core 逆像内に実精密化を持つ。 -/
lemma exists_verdierCoreCoconeRefinement {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C} (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ B.obj) (z : B.obj _⦋0⦌)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (D ≫ q.hom)) (hz : d.vertex = q.hom.app (Opposite.op ⦋0⦌) z)
    (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges d.val Set.univ) : Nonempty (VerdierCoreCoconeRefinement q D z d) := by
  obtain ⟨D', t, c, ht, hcz, l, hi, hp, hv⟩ :=
    exists_verdierSimplexCoconeLift_preservingPaths h D z d hz
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (c.val ≫ q.hom) d.val := by
    have := hi
    exact asIso (Truncated.HomotopyCategory.homMk l)
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (c.val ≫ q.hom) Set.univ :=
    (invertsEdges_functorIso_iff he Set.univ).mpr hd
  have hD' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (D' ≫ q.hom) Set.univ := by
    have hh := invertsAllEdges_precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0]) _ hc
    rw [← Category.assoc, c.property] at hh
    exact hh
  have hD : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (D ≫ q.hom) Set.univ := by
    have hh := invertsAllEdges_precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0]) _ hd
    rw [d.property] at hh
    exact hh
  let W := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).preimage q.hom
  let C' := corePreimageLift q.hom c.val hc
  have hprefix : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0] ≫ C' =
      corePreimageLift q.hom D' hD' := by
    apply (cancel_mono W.ι).mp
    rw [Category.assoc, corePreimageLift_ι, c.property]
    rfl
  have hti : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := (ihom (Δ[n] : SSet.{u})).obj C.obj)
      (t.map ((truncation 2).map ((ihom (Δ[n] : SSet.{u})).map q.hom))) := by
    change IsIso (simplexDenominatorImageIso q t ht).hom
    infer_instance
  let cW : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (corePreimageLift q.hom D' hD') := ⟨C', hprefix⟩
  have hq : cW.val ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).fromPreimage q.hom =
      allEdgesCoreLift (c.val ≫ q.hom) hc := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).ι).mp
    rw [Category.assoc, allEdgesCoreLift_ι]
    change (C' ≫ W.ι) ≫ q.hom = _
    rw [corePreimageLift_ι]
  let Hq := allEdgesCoreComparisonHomotopy l hi hc hd
  let Hq' : SSet.Homotopy
      (cW.val ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).fromPreimage q.hom)
      (allEdgesCoreLift d.val hd) := {
    h := Hq.h
    h₀ := Hq.h₀.trans hq.symm
    h₁ := Hq.h₁
    rel := Hq.rel }
  exact ⟨{
    source := D'
    denominator := t
    denominator_mem := ht
    cone := c
    apex_eq := hcz
    source_inverts := hD'
    original_inverts := hD
    cone_inverts := hc
    target_inverts := hd
    weakCone := cW
    weakCone_ι := corePreimageLift_ι q.hom c.val hc
    weakComparison := corePreimageComparisonHomotopy q.hom t hti hD' hD
    weakComparison_ι := corePreimageComparisonHomotopy_ι q.hom t hti hD' hD
    comparison := l
    comparison_invertible := hi
    comparison_prefix := hp
    comparison_apex := hv
    quotientComparison := Hq'
    quotientComparison_ι := allEdgesCoreComparisonHomotopy_ι l hi hc hd }⟩

end SerrePositivity.KST.LocalizingInvariants
