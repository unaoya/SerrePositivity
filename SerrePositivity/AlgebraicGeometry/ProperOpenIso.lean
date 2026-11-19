module

public meta import SerrePositivity.Util.DeprecatedAlias
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
概要：Stacks 081T の最後の段階で用いる固有な開埋め込みの同型性。
方針：稠密な開部分上の同型から像の稠密性を得て、固有性による閉像性と合わせる。
規約：ここでは位相的稠密性で足りる段階だけを扱う。
使われ方：平坦化後の strict transform と blowup 基底の同定。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/--
概要：固有な開埋め込みが稠密な開部分上で同型なら全体で同型。
方針：制限の全射性から稠密な開部分を像に含め、閉像性で全射性を得る。
規約：Stacks 081T Lemma 38.31.4 の最後の同定。被約性は不要。
使われ方：開部分スキームとなった strict transform を blowup 基底全体と同定する。
-/
theorem isIso_of_proper_openImmersion_dense_restrict {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] [IsOpenImmersion f] (U : Y.Opens)
    [IsIso (f ∣_ U)] (hU : Dense U.carrier) : IsIso f := by
  have hsub : U.carrier ⊆ Set.range f := by
    intro y hy
    obtain ⟨x, hx⟩ := (f ∣_ U).homeomorph.surjective ⟨y, hy⟩
    refine ⟨x.1, ?_⟩
    calc
      f x.1 = ((f ⁻¹ᵁ U).ι ≫ f) x := rfl
      _ = ((f ∣_ U) ≫ U.ι) x := congrArg (fun k => k x) (morphismRestrict_ι f U).symm
      _ = y := congrArg U.ι hx
  have hclosed : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top f
  apply TopologicalSpace.Opens.ext
  apply Set.eq_univ_of_forall
  intro y
  exact closure_minimal hsub hclosed (hU y)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
