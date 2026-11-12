module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseSSetMaps
public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
概要：内ホーンの充填条件による quasicategory 性の宇宙持ち上げ。
方針：元の面の互換性を保ってホーンを降ろし、同じ充填単体を持ち上げる。
規約：既存の F1 の深層定義に依存しない新規の葉。モデル構造を仮定しない。
使われ方：局所化を持ち上げた標的で試験する。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

def uliftSimplexHomDown {X : SSet.{u}} {n : ℕ}
    (f : (Δ[n] : SSet.{max u v}) ⟶ SSet.uliftFunctor.{v, u}.obj X) :
    (Δ[n] : SSet.{u}) ⟶ X :=
  SSet.yonedaEquiv.symm (SSet.yonedaEquiv f).down

lemma uliftSimplexHomDown_face {X : SSet.{u}} {n : ℕ}
    (f : (Δ[n + 1] : SSet.{max u v}) ⟶ SSet.uliftFunctor.{v, u}.obj X)
    (j : Fin (n + 2)) :
    stdSimplex.δ j ≫ uliftSimplexHomDown f =
      uliftSimplexHomDown (stdSimplex.δ j ≫ f) := by
  apply SSet.yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp]
  simp only [uliftSimplexHomDown, Equiv.apply_symm_apply,
    stdSimplex.yonedaEquiv_δ_comp]
  rfl

instance quasicategory_ulift_obj (X : SSet.{u}) [Quasicategory X] :
    Quasicategory (SSet.uliftFunctor.{v, u}.obj X) where
  hornFilling' n i a h0 hn := by
    let f := fun j hj ↦ horn.ι i j hj ≫ a
    have hf : horn.IsCompatible f := horn.IsCompatible.of_hom a
    have hF : horn.IsCompatible (fun j hj ↦ uliftSimplexHomDown (f j hj)) := by
      intro j k hj hk hjk
      rw [uliftSimplexHomDown_face, uliftSimplexHomDown_face, hf j k hj hk hjk]
    obtain ⟨φ, hφ⟩ := Quasicategory.hornFilling h0 hn hF.desc
    refine ⟨SSet.yonedaEquiv.symm (ULift.up (SSet.yonedaEquiv φ)), ?_⟩
    apply horn.hom_ext'
    intro j hj
    rw [horn.ι_ι_assoc]
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
    change SSet.yonedaEquiv (f j hj) = ULift.up (X.δ j (SSet.yonedaEquiv φ))
    apply ULift.ext
    have h := congrArg (fun q ↦ SSet.yonedaEquiv (horn.ι i j hj ≫ q)) hφ
    rw [hF.ι_desc, horn.ι_ι_assoc, stdSimplex.yonedaEquiv_δ_comp] at h
    simpa only [uliftSimplexHomDown, Equiv.apply_symm_apply] using h

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
