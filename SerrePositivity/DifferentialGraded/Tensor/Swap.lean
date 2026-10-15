module
public import SerrePositivity.DifferentialGraded.Tensor.SwapFamilies
public import SerrePositivity.DifferentialGraded.Tensor.ElementMap

/-! # opposite上のbalanced tensorとの符号付き交換同型 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 左右の因子を交換し、Dᵒᵖ上のbalanced tensorへ降ろす。 -/
def swapHom (M : RightModule A D) (N : LeftModule A D) :
    obj A D M N ⟶ obj A Dᵒᵖ N.toRightOpposite M.toFunctor :=
  desc A D M N (swapFamily A D M N
    ⟨ι A Dᵒᵖ N.toRightOpposite M.toFunctor, condition A Dᵒᵖ N.toRightOpposite M.toFunctor⟩)

/-- opposite上のtensorから元の順序へ戻す。 -/
def unswapHom (M : RightModule A D) (N : LeftModule A D) :
    obj A Dᵒᵖ N.toRightOpposite M.toFunctor ⟶ obj A D M N :=
  desc A Dᵒᵖ N.toRightOpposite M.toFunctor
    (unswapFamily A D M N ⟨ι A D M N, condition A D M N⟩)

@[reassoc (attr := simp)]
lemma ι_swapHom (M : RightModule A D) (N : LeftModule A D) (x : D) :
    ι A D M N x ≫ swapHom A D M N =
      (signedSwap (M.obj (op x)) (N.obj x)).hom ≫
        ι A Dᵒᵖ N.toRightOpposite M.toFunctor (op x) :=
  ι_desc A D M N _ x

@[reassoc (attr := simp)]
lemma ι_unswapHom (M : RightModule A D) (N : LeftModule A D) (x : Dᵒᵖ) :
    ι A Dᵒᵖ N.toRightOpposite M.toFunctor x ≫ unswapHom A D M N =
      (signedSwap (N.obj x.unop) (M.obj x)).hom ≫ ι A D M N x.unop :=
  ι_desc A Dᵒᵖ N.toRightOpposite M.toFunctor _ x

lemma swapHom_element (M : RightModule A D) (N : LeftModule A D) (x : D)
    {r s n : ℤ} (m : (M.obj (op x)).X r) (t : (N.obj x).X s) (hn : r + s = n) :
    (swapHom A D M N).f n (element A D M N x m t hn) =
      (r * s).negOnePow • element A Dᵒᵖ N.toRightOpposite M.toFunctor (op x) t m (by omega) := by
  have h := element_postcompose A D M N x (swapHom A D M N)
    (swapFamilyApp A D M N (ι A Dᵒᵖ N.toRightOpposite M.toFunctor) x)
    (ι_swapHom A D M N x) m t hn
  exact h.trans (swapFamilyApp_element A D M N _ x m t hn)

lemma unswapHom_element (M : RightModule A D) (N : LeftModule A D) (x : Dᵒᵖ)
    {s r n : ℤ} (t : (N.obj x.unop).X s) (m : (M.obj x).X r) (hn : s + r = n) :
    (unswapHom A D M N).f n (element A Dᵒᵖ N.toRightOpposite M.toFunctor x t m hn) =
      (s * r).negOnePow • element A D M N x.unop m t (by omega) := by
  have h := element_postcompose A Dᵒᵖ N.toRightOpposite M.toFunctor x (unswapHom A D M N)
    (unswapFamilyApp A D M N (ι A D M N) x) (ι_unswapHom A D M N x) t m hn
  exact h.trans (unswapFamilyApp_element A D M N _ x t m hn)

/-- 任意可換環上の非有界balanced tensorのopposite交換同型。 -/
def swapIso (M : RightModule A D) (N : LeftModule A D) :
    obj A D M N ≅ obj A Dᵒᵖ N.toRightOpposite M.toFunctor where
  hom := swapHom A D M N
  inv := unswapHom A D M N
  hom_inv_id := by
    apply hom_ext A D M N
    intro x
    rw [ι_swapHom_assoc, ι_unswapHom, ← Category.assoc,
      SerrePositivity.cochainTensorSymmetry_hom_comp]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  inv_hom_id := by
    apply hom_ext A Dᵒᵖ N.toRightOpposite M.toFunctor
    intro x
    rw [ι_unswapHom_assoc, ι_swapHom, ← Category.assoc,
      SerrePositivity.cochainTensorSymmetry_hom_comp]
    exact (Category.id_comp _).trans (Category.comp_id _).symm

end SerrePositivity.DifferentialGraded.BalancedTensor
