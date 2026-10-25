module
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanHom
/-!
概要：追加微分と可換な全次数 Hom 族を、両端の MC 変形後の Hom 鎖写像へ送る。
方針：元の graded cochain の線形同値と、変形 Hom の微分式を使う。
規約：次数零だけでなく全ての次数と符号付き可換式を保持する。
使われ方：D-8 c2 の変形 dg 加群の全 Hom 作用。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Preadditive HomologicalComplex CochainComplex HomComplex
variable {R : Type u} [CommRing R] {K L : Complex R}
  (θ : Cochain K K 1) (ψ : Cochain L L 1)
  (hθ : δ 1 2 θ + θ.comp θ (show (1 : ℤ) + 1 = 2 from rfl) = 0)
  (hψ : δ 1 2 ψ + ψ.comp ψ (show (1 : ℤ) + 1 = 2 from rfl) = 0)

def maurerCartanCochainEquiv (p : ℤ) : Cochain K L p ≃ₗ[R]
    Cochain (maurerCartanPerturbComplex K θ hθ) (maurerCartanPerturbComplex L ψ hψ) p where
  toFun := maurerCartanRebaseCochain θ ψ hθ hψ
  invFun := maurerCartanForgetCochain θ ψ hθ hψ
  left_inv f := by apply Cochain.ext; intro i j h; rfl
  right_inv f := by apply Cochain.ext; intro i j h; rfl
  map_add' f g := by apply Cochain.ext; intro i j h; rfl
  map_smul' a f := by apply Cochain.ext; intro i j h; rfl

def maurerCartanPerturbHomMap (T : Complex R) (f : T ⟶ homComplex R K L)
    (hf : ∀ (p : ℤ) (t : T.X p),
      (f.f p t).comp ψ rfl + (p + 1).negOnePow • θ.comp (f.f p t)
        (by omega : 1 + p = p + 1) = 0) :
    T ⟶ homComplex R (maurerCartanPerturbComplex K θ hθ)
      (maurerCartanPerturbComplex L ψ hψ) :=
  CochainComplex.ofHom
    (fun p => f.f p ≫ ModuleCat.ofHom (maurerCartanCochainEquiv θ ψ hθ hψ p).toLinearMap)
    (fun p => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro t
      apply (maurerCartanCochainEquiv θ ψ hθ hψ (p + 1)).symm.injective
      change maurerCartanForgetCochain θ ψ hθ hψ
        (δ p (p + 1) (maurerCartanRebaseCochain θ ψ hθ hψ (f.f p t))) =
          (f.f (p + 1)) (T.d p (p + 1) t)
      rw [maurerCartanHom_δ, add_assoc, hf p t, add_zero]
      exact ConcreteCategory.congr_hom (f.comm p (p + 1)) t)

end SerrePositivity.DifferentialGraded
