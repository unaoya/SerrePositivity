module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConnectiveCoverFunctor
public import SerrePositivity.KST.LocalizingInvariants.CochainConnectiveCoverElements
public import SerrePositivity.KST.LocalizingInvariants.CochainSurjectiveQuasiIsoLifts

/-!
概要：非正次数代数への次数全射準同型は、源の connective cover の後でも次数全射。
方針：負次数は元を持ち上げ、零次数は元の全射準同型の閉元持ち上げで補正する。
規約：零次数のホモロジー全射性だけで代用しない。使われ方：実 roof の非正次数化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {A B : Mon (Complex R)} [B.X.IsStrictlyLE 0]
  (p : A ⟶ B) (hs : ∀ n : ℤ, Function.Surjective (p.hom.f n)) (hq : QuasiIso p.hom)

include hs hq in
lemma connectiveCoverInclusion_comp_surjective (n : ℤ) :
    Function.Surjective (((connectiveCoverInclusion R A) ≫ p).hom.f n) := by
  intro y
  by_cases hn : n < 0
  · obtain ⟨x, hx⟩ := hs n y
    obtain ⟨z, hz⟩ := cochainTruncLE_lift_element R A.X n hn x
    exact ⟨z, (congrArg (p.hom.f n) hz).trans hx⟩
  · by_cases hzero : n = 0
    · subst n
      have hy : B.X.d 0 1 y = 0 := by
        have : Subsingleton (B.X.X 1) := ModuleCat.isZero_iff_subsingleton.1
          (B.X.isZero_of_isStrictlyLE 0 1 (by omega))
        exact Subsingleton.elim _ _
      obtain ⟨x, hx⟩ := cochain_cycle_lift_of_surjective_quasiIso p.hom hs hq 0 ⟨y, hy⟩
      obtain ⟨z, hz⟩ := cochainTruncLE_lift_cycle R A.X 0 (by omega) x
      exact ⟨z, (congrArg (p.hom.f 0) hz).trans hx⟩
    · have : Subsingleton (B.X.X n) := ModuleCat.isZero_iff_subsingleton.1
        (B.X.isZero_of_isStrictlyLE 0 n (by omega))
      exact ⟨0, Subsingleton.elim _ _⟩

include hq in
lemma connectiveCoverInclusion_comp_quasiIso :
    QuasiIso (((connectiveCoverInclusion R A) ≫ p).hom) := by
  have := hq
  have hm : QuasiIso (connectiveCoverMap R p).hom := by
    apply (CochainComplex.quasiIso_truncLEMap_iff p.hom 0).2
    intro i hi
    infer_instance
  have hb : QuasiIso (connectiveCoverInclusion R B).hom :=
    connectiveCoverInclusion_quasiIso R B (by change B.X.IsLE 0; infer_instance)
  have he := (connectiveCoverCounit R).naturality p
  change connectiveCoverMap R p ≫ connectiveCoverInclusion R B =
    connectiveCoverInclusion R A ≫ p at he
  rw [← he]
  exact quasiIso_comp _ _ (hφ := hm) (hφ' := hb)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
