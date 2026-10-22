module

public import SerrePositivity.InfinityCategories.F2.Ind.PointSliceKanComparison
public import SerrePositivity.InfinityCategories.F1B.KanLeftUnitInvertible

/-!
概要：任意の充満忠実な元の関手に沿う左 Kan 拡張の、指定単位自体が可逆。
方針：元の slice の恒等終対象を比較同値で移し、既存の脚と成分の比較を使う。
規約：元の関手の inner fibration 性を要求しない。
使われ方：Indκ への構成済み左 Kan 延長を元の Yoneda 上で回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
open F1B

/-- 充満忠実な元の関手の像の局所 Kan 添字では、元の恒等頂点が終対象。 -/
lemma leftKanIdentity_isTerminal_of_fullyFaithful {K C : SSet.{u}}
    [Quasicategory K] [Quasicategory C] (δ : K ⟶ C) (hδ : IsFullyFaithful δ) (k : K _⦋0⦌) :
    IsTerminalVertex (kanLeftKanIdentityVertex δ k) := by
  have h := (pointSliceKanComparison_isQCatEquivalence δ k hδ).choose.map_isTerminalVertex
    (kanSliceIdentityCone_isTerminalVertex k)
  change IsTerminalVertex ((pointSliceKanComparison δ k).app (Opposite.op ⦋0⦌)
    (sliceIdentityCone k)) at h
  rw [pointSliceKanComparison_identity] at h
  exact h

/-- 同じ局所輸送余錐の恒等頂点の脚を使い、指定単位の同じ成分が可逆と判定する。 -/
lemma leftKanTransport_unit_component_isIso_of_fullyFaithful {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D]
    (δ : K ⟶ C) (hδ : IsFullyFaithful δ)
    {F₀ : K ⟶ D} {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)}
    (k : K _⦋0⦌) (t : LeftKanCoconeTransport δ F₀ F β (δ.app (Opposite.op ⦋0⦌) k))
    (ht : IsColimitCone t.cocone) :
    IsIso (functorHomEvaluate
      (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β)) k) := by
  let a := kanLeftKanIdentityVertex δ k
  let L := leftKanShape δ (δ.app (Opposite.op ⦋0⦌) k)
  let α := SSet.Truncated.HomotopyCategory.homMk t.edge
  have hc := kanColimit_terminal_leg_invertible t.cocone ht a
    (leftKanIdentity_isTerminal_of_fullyFaithful δ hδ k)
  have hd := kanLeftCanonical_identity_leg_invertible δ F k
  have ha : IsIso (functorHomEvaluate α (SSet.yonedaEquiv (joinInr L (Δ[0] : SSet.{u})))) := by
    have := kanLeftTransport_apex_isIso t
    unfold functorHomEvaluate
    change IsIso (eqToHom _ ≫
      (hoFunctor.map (coconeApexEvaluation L D)).toFunctor.map α ≫ eqToHom _)
    infer_instance
  have hs := kanCoconeHom_source_component_isIso t.cocone
    (leftKanCanonicalCocone δ F (δ.app (Opposite.op ⦋0⦌) k)) α
    (SSet.yonedaEquiv.symm a) hc hd ha
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at hs
  have hu := (kanLeftTransport_source_component_isIso_iff t a).1 hs
  dsimp only [a] at hu
  rw [kanLeftKanIdentityVertex_projection] at hu
  exact hu

/-- 任意の充満忠実な元の関手に沿う左 Kan 拡張の指定単位自体が、関手圏で可逆。 -/
lemma leftKanExtension_unit_isIso_of_fullyFaithful {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D]
    (δ : K ⟶ C) (hδ : IsFullyFaithful δ)
    {F₀ : K ⟶ D} {F : C ⟶ D} (β : SSet.Homotopy F₀ (δ ≫ F))
    (hβ : IsLeftKanExtension δ F₀ F β) :
    IsIso (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β)) := by
  change IsInvertibleEdge (functorEdgeOfSimplicialHomotopy β)
  apply (isInvertibleEdge_iff_evaluateFunctorAt (functorEdgeOfSimplicialHomotopy β)).2
  intro k
  obtain ⟨t, ht⟩ := hβ (δ.app (Opposite.op ⦋0⦌) k)
  exact (kanFunctorHomEvaluate_isIso_iff _ k).1
    (leftKanTransport_unit_component_isIso_of_fullyFaithful δ hδ k t ht)

end SerrePositivity.InfinityCategories.F2.Ind
