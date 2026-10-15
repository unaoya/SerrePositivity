module
public import SerrePositivity.DifferentialGraded.Tensor.ElementsExt

/-! # 包含で指定した射の純粋斉次元への評価 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma element_postcompose (M : RightModule A D) (N : LeftModule A D) (x : D)
    {T : Complex A} (f : obj A D M N ⟶ T) (g : objectFamily A D M N x ⟶ T)
    (h : ι A D M N x ≫ f = g) {r s n : ℤ}
    (m : (M.obj (op x)).X r) (v : (N.obj x).X s) (hn : r + s = n) :
    f.f n (element A D M N x m v hn) =
      g.f n (ιTensorObj (M.obj (op x)) (N.obj x) r s n hn (m ⊗ₜ[A] v)) :=
  congrArg (fun k => k.f n
    (ιTensorObj (M.obj (op x)) (N.obj x) r s n hn (m ⊗ₜ[A] v))) h

/-- 主Hom自然性の等式を純粋生成元での前後合成へ帰着する。 -/
lemma homMap_post_pre_eq (M : RightModule A D) (N : LeftModule A D)
    {K P Q T : Complex A} (F : K ⟶ homComplex A (obj A D M N) P)
    (G : K ⟶ homComplex A Q T) (f : P ⟶ T) (g : obj A D M N ⟶ Q)
    (h : ∀ (k : ℤ) (t : K.X k) (x : D) (r s a n : ℤ) (ha : r + s = a) (hn : a + k = n)
      (m : (M.obj (op x)).X r) (v : (N.obj x).X s),
      f.f n (((F.f k t).v a n hn) (element A D M N x m v ha)) =
      (G.f k t).v a n hn (g.f a (element A D M N x m v ha))) :
    F ≫ homPostcompose (obj A D M N) f = G ≫ homPrecompose g T := by
  apply HomologicalComplex.hom_ext
  intro k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  change (homPostcompose _ f).f k (F.f k t) = (homPrecompose g _).f k (G.f k t)
  rw [homPostcompose_apply, homPrecompose_apply]
  apply cochain_element_ext A D M N
  intro x r s a n ha hn m v
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    Cochain.ofHom_v]
  exact h k t x r s a n ha hn m v

end SerrePositivity.DifferentialGraded.BalancedTensor
