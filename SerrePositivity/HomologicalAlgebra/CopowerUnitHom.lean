module
public import SerrePositivity.HomologicalAlgebra.FreePresheafFunctor
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Module.Equiv.Basic

/-!
概要：単位加群の指定余積からの射を、各生成元の像の族として表示する。
方針：余積の普遍性と単位加群からの線形射の評価を合成する。
規約：添字集合は小さい宇宙、係数加群は任意の宇宙。生成元は指定余積包含の1の像。
使われ方：HA 1.2.4、G10 の BK 係数重みから単体集合の写像への比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
namespace SerrePositivity.HomologicalAlgebra
variable (A : Type u) [CommRing A] (S : Type) (M : ModuleCat.{u} A)

/-- 単位加群の余積からの射を生成元の像で表示する同値。 -/
def copowerUnitHomEquiv : ((copowerFunctor (ModuleCat.of A A)).obj S ⟶ M) ≃ (S → M) where
  toFun f s := f (Sigma.ι (fun _ : S => ModuleCat.of A A) s (1 : A))
  invFun g := Sigma.desc (fun s => ModuleCat.ofHom ((LinearMap.ringLmapEquivSelf A A M).symm (g s)))
  left_inv f := by
    apply Sigma.hom_ext
    intro s
    rw [Sigma.ι_comp_desc]
    apply ModuleCat.hom_ext
    apply (LinearMap.ringLmapEquivSelf A A M).injective
    exact (LinearMap.ringLmapEquivSelf A A M).apply_symm_apply _
  right_inv g := by
    funext s
    have h := congrArg (fun f => f (1 : A))
      (Sigma.ι_comp_desc (fun s => ModuleCat.ofHom ((LinearMap.ringLmapEquivSelf A A M).symm (g s))) s)
    exact h.trans ((LinearMap.ringLmapEquivSelf A A M).apply_symm_apply (g s))

/-- 同じ生成元評価は標的の全線形射による後合成と可換。 -/
theorem copowerUnitHomEquiv_postcomp {M N : ModuleCat.{u} A}
    (f : (copowerFunctor (ModuleCat.of A A)).obj S ⟶ M) (g : M ⟶ N) :
    copowerUnitHomEquiv A S N (f ≫ g) = fun s => g (copowerUnitHomEquiv A S M f s) := rfl

/-- 添字写像による余積の射は、同じ生成元の添字替えに対応する。 -/
theorem copowerUnitHomEquiv_precomp {S T : Type} (h : S ⟶ T)
    (f : (copowerFunctor (ModuleCat.of A A)).obj T ⟶ M) :
    copowerUnitHomEquiv A S M ((copowerFunctor (ModuleCat.of A A)).map h ≫ f) =
      fun s => copowerUnitHomEquiv A T M f (h s) := by
  funext s
  have he : Sigma.ι (fun _ : S => ModuleCat.of A A) s ≫
      (copowerFunctor (ModuleCat.of A A)).map h =
      Sigma.ι (fun _ : T => ModuleCat.of A A) (h s) := by
    simp [copowerFunctor]
  exact congrArg (fun k => f (k (1 : A))) he

end SerrePositivity.HomologicalAlgebra
