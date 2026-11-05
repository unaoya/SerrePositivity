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
structure VerdierCoreCoconeRefinement {B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C) {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ B.obj)
    (z : B.obj _⦋0⦌) (d : JoinCocone (D ≫ q.hom)) where
  source : (Δ[n] : SSet.{u}) ⟶ B.obj
  denominator : Truncated.Edge (X := (truncation 2).obj ((ihom (Δ[n] : SSet.{u})).obj B.obj))
    (functorVertex source) (functorVertex D)
  denominator_mem : denominator.edge ∈
    (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌)
  cone : JoinCocone source
  apex_eq : cone.vertex = z
  source_inverts : InvertsEdges (source ≫ q.hom) Set.univ
  original_inverts : InvertsEdges (D ≫ q.hom) Set.univ
  cone_inverts : InvertsEdges (cone.val ≫ q.hom) Set.univ
  target_inverts : InvertsEdges d.val Set.univ
  weakCone : JoinCocone (corePreimageLift q.hom source source_inverts)
  weakCone_ι : weakCone.val ≫ ((quasicategoryCore C.obj).preimage q.hom).ι = cone.val
  weakComparison : SSet.Homotopy (corePreimageLift q.hom source source_inverts)
    (corePreimageLift q.hom D original_inverts)
  weakComparison_ι : weakComparison.h ≫ ((quasicategoryCore C.obj).preimage q.hom).ι =
    (simplicialHomotopyOfFunctorEdge denominator).h
  comparison : Truncated.Edge
    (X := (truncation 2).obj ((ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj))
    (functorVertex (cone.val ≫ q.hom)) (functorVertex d.val)
  comparison_invertible : IsInvertibleEdge
    (X := (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj) comparison
  comparison_prefix : ((pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj).app
    (Opposite.op ⦋1⦌) comparison.edge =
      ((ihom (Δ[n] : SSet.{u})).map q.hom).app (Opposite.op ⦋1⦌) denominator.edge
  comparison_apex : SSet.yonedaEquiv.symm comparison.edge ≫
    (pre (joinInr (Δ[n] : SSet.{u}) Δ[0])).app C.obj =
      curry (snd (Δ[0] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm
        (C.obj.σ 0 (q.hom.app (Opposite.op ⦋0⦌) z)))
  quotientComparison : SSet.Homotopy
    (weakCone.val ≫ (quasicategoryCore C.obj).fromPreimage q.hom)
    (allEdgesCoreLift d.val target_inverts)
  quotientComparison_ι : quotientComparison.h ≫ (quasicategoryCore C.obj).ι =
    (simplicialHomotopyOfFunctorEdge comparison).h

/-- 元の Verdier 商の可逆余錐は、全次数で元の core 逆像内に実精密化を持つ。 -/
lemma exists_verdierCoreCoconeRefinement {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}}
    {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C} (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q)
    {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ B.obj) (z : B.obj _⦋0⦌)
    (d : JoinCocone (D ≫ q.hom)) (hz : d.vertex = q.hom.app (Opposite.op ⦋0⦌) z)
    (hd : InvertsEdges d.val Set.univ) : Nonempty (VerdierCoreCoconeRefinement q D z d) := by
  obtain ⟨D', t, c, ht, hcz, l, hi, hp, hv⟩ :=
    exists_verdierSimplexCoconeLift_preservingPaths h D z d hz
  have he : FunctorIso (c.val ≫ q.hom) d.val := by
    have := hi
    exact asIso (Truncated.HomotopyCategory.homMk l)
  have hc : InvertsEdges (c.val ≫ q.hom) Set.univ :=
    (invertsEdges_functorIso_iff he Set.univ).mpr hd
  have hD' : InvertsEdges (D' ≫ q.hom) Set.univ := by
    have hh := invertsAllEdges_precomp (joinInl (Δ[n] : SSet.{u}) Δ[0]) _ hc
    rw [← Category.assoc, c.property] at hh
    exact hh
  have hD : InvertsEdges (D ≫ q.hom) Set.univ := by
    have hh := invertsAllEdges_precomp (joinInl (Δ[n] : SSet.{u}) Δ[0]) _ hd
    rw [d.property] at hh
    exact hh
  let W := (quasicategoryCore C.obj).preimage q.hom
  let C' := corePreimageLift q.hom c.val hc
  have hprefix : joinInl (Δ[n] : SSet.{u}) Δ[0] ≫ C' =
      corePreimageLift q.hom D' hD' := by
    apply (cancel_mono W.ι).mp
    rw [Category.assoc, corePreimageLift_ι, c.property]
    rfl
  have hti : IsInvertibleEdge (X := (ihom (Δ[n] : SSet.{u})).obj C.obj)
      (t.map ((truncation 2).map ((ihom (Δ[n] : SSet.{u})).map q.hom))) := by
    change IsIso (simplexDenominatorImageIso q t ht).hom
    infer_instance
  let cW : JoinCocone (corePreimageLift q.hom D' hD') := ⟨C', hprefix⟩
  have hq : cW.val ≫ (quasicategoryCore C.obj).fromPreimage q.hom =
      allEdgesCoreLift (c.val ≫ q.hom) hc := by
    apply (cancel_mono (quasicategoryCore C.obj).ι).mp
    rw [Category.assoc, allEdgesCoreLift_ι]
    change (C' ≫ W.ι) ≫ q.hom = _
    rw [corePreimageLift_ι]
  let Hq := allEdgesCoreComparisonHomotopy l hi hc hd
  let Hq' : SSet.Homotopy
      (cW.val ≫ (quasicategoryCore C.obj).fromPreimage q.hom)
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
