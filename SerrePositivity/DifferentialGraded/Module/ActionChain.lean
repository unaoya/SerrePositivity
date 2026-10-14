module
public import SerrePositivity.DifferentialGraded.Module.ClosedMaps

/-! # 全次数作用を tensor の chain map として読む -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 全次数の右作用の符号なし転置。 -/
abbrev moduleActionChain (M : RightModule A D) (x y : Dᵒᵖ) :
    (x ⟶[Complex A] y) ⊗ M.obj x ⟶ M.obj y := uncurryRight (M.map x y)

/-- 全次数自然な chain map 族は tensor 作用の chain map と可換。 -/
lemma closedFamily_action_chain {M N : RightModule A D}
    (a : ∀ x : Dᵒᵖ, M.obj x ⟶ N.obj x)
    (h : ∀ x y : Dᵒᵖ, M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y)) (x y : Dᵒᵖ) :
    moduleActionChain A M x y ≫ a y =
      (𝟙 (x ⟶[Complex A] y) ⊗ₘ a x) ≫ moduleActionChain A N x y := by
  apply (tensorRightHomEquiv (M.obj x) (x ⟶[Complex A] y) (N.obj y)).injective
  change curryRight (uncurryRight (M.map x y) ≫ a y) =
    curryRight ((𝟙 (x ⟶[Complex A] y) ⊗ₘ a x) ≫ uncurryRight (N.map x y))
  rw [curryRight_naturality_target, curryRight_naturality_domain,
    curryRight_uncurryRight, curryRight_uncurryRight]
  exact h x y

variable (D) [Small.{u} D]
/-- 加群圏の実際の射は全次数 tensor 作用と可換。 -/
lemma moduleMorphism_action_chain {M N : ModuleCategory A D} (f : M ⟶ N) (x y : Dᵒᵖ) :
    moduleActionChain A (ForgetEnrichment.to (Complex A) M) x y ≫
      (moduleEvaluation A D y.unop).map f =
    (𝟙 (x ⟶[Complex A] y) ⊗ₘ (moduleEvaluation A D x.unop).map f) ≫
      moduleActionChain A (ForgetEnrichment.to (Complex A) N) x y :=
  closedFamily_action_chain A (closedTransApp A (moduleClosedHomEquiv A D M N f))
    (closedTransApp_naturality A (moduleClosedHomEquiv A D M N f)) x y
end SerrePositivity.DifferentialGraded
