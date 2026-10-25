module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConvolutionConstant
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConvolutionContravariant

/-!
概要：定数単体の余モノイド・標的代数に対する全自然性。
方針：元の余単位の保存と tensor 余単位比較の自然性を転置する。
規約：底の代数射と全単体作用素を保つ。
使われ方：指定底上の相対乗法的写像の単体集合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open scoped ComonObj
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R]

lemma convolutionConstantMap_precompose {H K : Comon (Complex R)} (f : H ⟶ K)
    (B : Mon (Complex R)) :
    convolutionConstantMap R K B ≫ convolutionPrecompose R f B =
      convolutionConstantMap R H B := by
  apply Mon.Hom.ext'
  change MonoidalClosed.curry (A := K.X) ((convolutionTensorCounit R K).app B.X) ≫
      (MonoidalClosed.pre f.hom).app B.X =
      MonoidalClosed.curry (A := H.X) ((convolutionTensorCounit R H).app B.X)
  simp only [convolutionTensorCounit_app]
  calc
    _ = MonoidalClosed.curry (A := H.X)
        (f.hom ▷ B.X ≫ (ε[K.X] ▷ B.X ≫ (λ_ B.X).hom)) :=
      MonoidalClosed.curry_pre_app f.hom (ε[K.X] ▷ B.X ≫ (λ_ B.X).hom)
    _ = _ := by
      congr 1
      rw [← comp_whiskerRight_assoc, IsComonHom.hom_counit]


lemma convolutionConstantMap_naturality (H : Comon (Complex R))
    {B C : Mon (Complex R)} (g : B ⟶ C) :
    convolutionConstantMap R H B ≫ (convolutionFunctor R H).map g =
      g ≫ convolutionConstantMap R H C := by
  apply Mon.Hom.ext'
  change MonoidalClosed.curry (A := H.X) ((convolutionTensorCounit R H).app B.X) ≫
      (ihom H.X).map g.hom = g.hom ≫
      MonoidalClosed.curry (A := H.X) ((convolutionTensorCounit R H).app C.X)
  rw [← MonoidalClosed.curry_natural_right, ← MonoidalClosed.curry_natural_left]
  congr 1
  exact
    ((convolutionTensorCounit R H).naturality g.hom).symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
