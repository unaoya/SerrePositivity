module
public import SerrePositivity.DifferentialGraded.Tensor.ElementsExt

/-! # balanced tensorの各次数からの線形射の外延性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Limits MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (M : RightModule A D) (N : LeftModule A D)

/-- 出力次数や微分との可換性を仮定せず、固定次数の線形射を生成元で判定する。 -/
lemma degree_element_ext {a : ℤ} {V : ModuleCat.{u} A}
    (f g : (obj A D M N).X a ⟶ V)
    (h : ∀ (x : D) (r s : ℤ) (ha : r + s = a)
      (m : (M.obj (op x)).X r) (v : (N.obj x).X s),
      f (element A D M N x m v ha) = g (element A D M N x m v ha)) : f = g := by
  let : Epi (projection A D M N) := by
    dsimp [projection]
    infer_instance
  apply (cancel_epi ((projection A D M N).f a)).mp
  apply (isColimitOfPreserves (HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) a)
    (colimit.isColimit (Discrete.functor (objectFamily A D M N)))).hom_ext
  intro x
  change (Sigma.ι (objectFamily A D M N) x.as).f a ≫ (projection A D M N).f a ≫ f =
    (Sigma.ι (objectFamily A D M N) x.as).f a ≫ (projection A D M N).f a ≫ g
  apply mapBifunctor.hom_ext
  intro r s ha
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro m v
  exact h x.as r s ha m v

end SerrePositivity.DifferentialGraded.BalancedTensor
