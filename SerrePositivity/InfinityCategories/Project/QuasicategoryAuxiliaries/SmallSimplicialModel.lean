module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.SmallSubcomplexStages
public import Mathlib.AlgebraicTopology.Quasicategory.Basic

/-!
概要：各次数が小さい実単体集合を、同じ単体・面・退化を持つ小さい宇宙へ移す。
方針：次数ごとの Shrink と自然な全単射を使い、全内ホーンの互換性を保って充填する。
規約：straightening・モデル構造・局所化に依存しない。
使われ方：Ind-S (4) の小さい充填閉包の標的模型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 元の次数ごとの全単射を使う小さい単体模型。 -/
abbrev model (X : SSet.{v}) [∀ d, Small.{u} (X.obj d)] : SSet.{u} :=
  FunctorToTypes.shrink X

/-- 小さい標準単体からの射を、同じ元の ambient 単体へ戻す。 -/
def simplexToAmbient {X : SSet.{v}} [∀ d, Small.{u} (X.obj d)] {n : ℕ}
    (f : (Δ[n] : SSet.{u}) ⟶ model X) : (Δ[n] : SSet.{v}) ⟶ X :=
  SSet.yonedaEquiv.symm ((equivShrink.{u} _).symm (SSet.yonedaEquiv f))

lemma simplexToAmbient_face {X : SSet.{v}} [∀ d, Small.{u} (X.obj d)] {n : ℕ}
    (f : (Δ[n + 1] : SSet.{u}) ⟶ model X) (j : Fin (n + 2)) :
    stdSimplex.δ j ≫ simplexToAmbient f = simplexToAmbient (stdSimplex.δ j ≫ f) := by
  apply SSet.yonedaEquiv.injective
  simp only [simplexToAmbient, stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
  change X.δ j ((equivShrink.{u} (X _⦋n + 1⦌)).symm (SSet.yonedaEquiv f)) =
    (equivShrink.{u} (X _⦋n⦌)).symm (equivShrink.{u} (X _⦋n⦌)
      (X.δ j ((equivShrink.{u} (X _⦋n + 1⦌)).symm (SSet.yonedaEquiv f))))
  rw [Equiv.symm_apply_apply]

/-- 小さい模型は元の quasicategory の同じ充填単体を回収する。 -/
instance model_quasicategory (X : SSet.{v}) [∀ d, Small.{u} (X.obj d)] [Quasicategory X] :
    Quasicategory (model X) where
  hornFilling' {n i} a h0 hn := by
    let f := fun j hj => horn.ι i j hj ≫ a
    have hf : horn.IsCompatible f := horn.IsCompatible.of_hom a
    have hc : horn.IsCompatible (fun j hj => simplexToAmbient.{u, v} (f j hj)) := by
      intro j k hj hk hjk
      rw [simplexToAmbient_face, simplexToAmbient_face, hf j k hj hk hjk]
    obtain ⟨φ, hφ⟩ := Quasicategory.hornFilling h0 hn hc.desc
    refine ⟨SSet.yonedaEquiv.symm (equivShrink.{u} _ (SSet.yonedaEquiv φ)), ?_⟩
    apply horn.hom_ext'
    intro j hj
    rw [horn.ι_ι_assoc]
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
    change SSet.yonedaEquiv (f j hj) = equivShrink.{u} (X _⦋n + 1⦌)
      (X.δ j ((equivShrink.{u} (X _⦋n + 2⦌)).symm
        (equivShrink.{u} (X _⦋n + 2⦌) (SSet.yonedaEquiv φ))))
    rw [Equiv.symm_apply_apply]
    apply (equivShrink.{u} _).symm.injective
    rw [Equiv.symm_apply_apply]
    have h := congrArg (fun q => SSet.yonedaEquiv (horn.ι i j hj ≫ q)) hφ
    rw [hc.ι_desc, horn.ι_ι_assoc, stdSimplex.yonedaEquiv_δ_comp] at h
    simpa only [simplexToAmbient, Equiv.apply_symm_apply] using h

/-- 宇宙持ち上げした小さい模型と、元の全単体集合との厳密な同型。 -/
def modelIso (X : SSet.{max u v}) [∀ d, Small.{u} (X.obj d)] :
    (SSet.uliftFunctor.{v, u}).obj (model X) ≅ X :=
  NatIso.ofComponents (fun d => Equiv.toIso {
    toFun := fun x => (equivShrink.{u} (X.obj d)).symm x.down
    invFun := fun x => ULift.up (equivShrink.{u} (X.obj d) x)
    left_inv := by intro x; apply ULift.ext; exact Equiv.apply_symm_apply _ _
    right_inv := by intro x; simp }) (by
      intro d e f
      apply ConcreteCategory.hom_ext
      intro x
      exact Equiv.symm_apply_apply _ _)

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
