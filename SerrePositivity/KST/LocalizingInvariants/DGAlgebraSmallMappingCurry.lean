module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSmallMappingCone

/-!
概要：実 AW 制限代数への射を、元の全単体上の乗法的写像へ移す。
方針：各標準単体への制限を取り、正本の米田自然性と関手則で照合する。
規約：小さい単体集合の宇宙の持ち上げを明示する。
使われ方：実ホーンの代数的持ち上げを元の単体集合の充填へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {A B : Mon (Complex R)} {K : SSet.{0}}
  (f : A ⟶ (simplicialConvolution R B).obj (op K))

def smallMultiplicativeMappingCurry :
    SSet.uliftFunctor.{u, 0}.obj K ⟶ multiplicativeMappingSimplices R A B where
  app n := TypeCat.ofHom (fun z =>
    f ≫ (simplicialConvolution R B).map (SSet.yonedaEquiv.{0}.symm z.down).op)
  naturality m n θ := by
    apply ConcreteCategory.hom_ext
    intro z
    change ULift.{u, 0} (K.obj m) at z
    change f ≫ (simplicialConvolution R B).map
        (SSet.yonedaEquiv.{0}.symm (K.map θ z.down)).op =
      (f ≫ (simplicialConvolution R B).map (SSet.yonedaEquiv.{0}.symm z.down).op) ≫
        (simplicialConvolution R B).map (SSet.stdSimplex.map θ.unop).op
    have hy := SSet.yonedaEquiv_symm_naturality_left (X := K) θ.unop z.down
    simp only [Quiver.Hom.op_unop] at hy
    rw [← hy, op_comp, (simplicialConvolution R B).map_comp, Category.assoc]

lemma smallMultiplicativeMappingCurry_app (n : SimplexCategoryᵒᵖ)
    (z : (SSet.uliftFunctor.{u, 0}.obj K).obj n) :
    (smallMultiplicativeMappingCurry R f).app n z =
      f ≫ (simplicialConvolution R B).map (SSet.yonedaEquiv.{0}.symm z.down).op := rfl

lemma smallMultiplicativeMappingCurry_density (i : (simplexConvolutionIndex K)ᵒᵖ) :
    (smallMultiplicativeMappingCurry R f).app (op i.unop.left)
        ⟨SSet.yonedaEquiv.{0} i.unop.hom⟩ =
      f ≫ (simplexConvolutionDensityCone R B K).π.app i := by
  rw [smallMultiplicativeMappingCurry_app, SSet.yonedaEquiv.symm_apply_apply]
  rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
