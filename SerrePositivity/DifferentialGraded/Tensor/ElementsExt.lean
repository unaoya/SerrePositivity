module
public import SerrePositivity.DifferentialGraded.Tensor.Elements
public import SerrePositivity.DifferentialGraded.Tensor.Parameter

/-! # balanced tensorを源とする全次数射の生成元による外延性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Limits MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (M : RightModule A D) (N : LeftModule A D)

/-- 微分と可換とは限らない斉次cochainも純粋生成元で判定できる。 -/
lemma cochain_element_ext {T : Complex A} {q : ℤ} (f g : Cochain (obj A D M N) T q)
    (h : ∀ (x : D) (r s a n : ℤ) (ha : r + s = a) (hn : a + q = n)
      (m : (M.obj (op x)).X r) (v : (N.obj x).X s),
      f.v a n hn (element A D M N x m v ha) =
        g.v a n hn (element A D M N x m v ha)) : f = g := by
  let : Epi (projection A D M N) := by
    dsimp [projection]
    infer_instance
  apply Cochain.ext
  intro a n hn
  apply (cancel_epi ((projection A D M N).f a)).mp
  apply (isColimitOfPreserves (HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) a)
    (colimit.isColimit (Discrete.functor (objectFamily A D M N)))).hom_ext
  intro x
  change (Sigma.ι (objectFamily A D M N) x.as).f a ≫ (projection A D M N).f a ≫ f.v a n hn =
    (Sigma.ι (objectFamily A D M N) x.as).f a ≫ (projection A D M N).f a ≫ g.v a n hn
  apply mapBifunctor.hom_ext
  intro r s ha
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro m v
  exact h x.as r s a n ha hn m v

/-- 次数零の場合は同じ入出力次数で判定できる。 -/
lemma cochain_zero_element_ext {T : Complex A} (f g : Cochain (obj A D M N) T 0)
    (h : ∀ (x : D) (r s a : ℤ) (ha : r + s = a)
      (m : (M.obj (op x)).X r) (v : (N.obj x).X s),
      f.v a a (add_zero a) (element A D M N x m v ha) =
        g.v a a (add_zero a) (element A D M N x m v ha)) : f = g := by
  let : Epi (projection A D M N) := by
    dsimp [projection]
    infer_instance
  apply Cochain.ext₀
  intro a
  apply (cancel_epi ((projection A D M N).f a)).mp
  apply (isColimitOfPreserves (HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) a)
    (colimit.isColimit (Discrete.functor (objectFamily A D M N)))).hom_ext
  intro x
  change (Sigma.ι (objectFamily A D M N) x.as).f a ≫ (projection A D M N).f a ≫
      f.v a a (add_zero a) =
    (Sigma.ι (objectFamily A D M N) x.as).f a ≫ (projection A D M N).f a ≫ g.v a a (add_zero a)
  apply mapBifunctor.hom_ext
  intro r s ha
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro m v
  exact h x.as r s a ha m v

/-- 主Homへのchain mapも各包含への前合成で判定できる。 -/
lemma homMap_ext {K T : Complex A} (f g : K ⟶ homComplex A (obj A D M N) T)
    (h : ∀ x, f ≫ homPrecompose (ι A D M N x) T =
      g ≫ homPrecompose (ι A D M N x) T) : f = g := by
  apply (tensorRightHomEquiv (obj A D M N) K T).symm.injective
  apply param_hom_ext
  intro x
  apply (tensorRightHomEquiv (objectFamily A D M N x) K T).injective
  change curryRight ((𝟙 K ⊗ₘ ι A D M N x) ≫ uncurryRight f) =
    curryRight ((𝟙 K ⊗ₘ ι A D M N x) ≫ uncurryRight g)
  rw [curryRight_naturality_domain, curryRight_naturality_domain,
    curryRight_uncurryRight, curryRight_uncurryRight]
  exact h x

end SerrePositivity.DifferentialGraded.BalancedTensor
