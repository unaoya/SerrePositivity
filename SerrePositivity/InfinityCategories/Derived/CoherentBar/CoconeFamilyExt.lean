module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLinearRecovery
public import SerrePositivity.InfinityCategories.Core.JoinCurryHomExt
/-!
概要：全混合単体による余錐族の外延性と、全写像空間比較の単射性を証明する。
方針：既存の join の curry 外延性と線形成分からの混合単体の復元を使う。
規約：全パラメーター次数を扱い、写像空間の同値性とは区別する。
使われ方：工程Bの逆比較の一意性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (y : (dgNerve R (RightModule R D)) _⦋0⦌)

lemma dgCoherentBarCoconeFamily_ext {m : ℕ}
    (c d : (coconeMappingSpace F y) _⦋m⦌)
    (h : ∀ {n : ℕ} (s : I _⦋n⦌), dgCoherentBarCoconeFamilySimplex R D F y c s =
      dgCoherentBarCoconeFamilySimplex R D F y d s) : c = d := by
  apply Subtype.ext
  apply Subtype.ext
  apply join_left_hom_ext
  · apply SSet.yonedaEquiv.injective
    exact c.property.trans d.property.symm
  · intro n a
    obtain ⟨s, rfl⟩ := (SSet.yonedaEquiv
      (X := (SSet.uliftFunctor.{max (u + 1) v, u}).obj I)).symm.surjective a
    apply (cancel_epi (joinStdSimplexIso n m).inv).1
    apply SSet.yonedaEquiv.injective
    exact h s.down

lemma dgCoherentBarCoconeHomSpaceComparison_injective
    (hMC : dgCoherentBarMaurerCartan R D F) (n : ℕ) :
    Function.Injective ((dgCoherentBarCoconeHomSpaceComparison R D F hMC y).app
      (Opposite.op ⦋n⦌)) := by
  intro c d h
  have hData := congrArg DGNerve.PinchedHom.toLinearData h
  rw [dgCoherentBarCoconeHomSpaceComparison_linear,
    dgCoherentBarCoconeHomSpaceComparison_linear] at hData
  apply dgCoherentBarCoconeFamily_ext R D F y c d
  intro m s
  exact dgCoherentBarCoconeFamilySimplex_eq_of_linearData R D F hMC y c d hData s

end SerrePositivity.InfinityCategories
