module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConvolutionFunctor

/-!
概要：余モノイドに反変・dg 代数に共変な畳み込み関手。
方針：内部 Hom の元の前合成を代数射に束ねる。
規約：恒等・合成・代数側の自然性を全射で保持する。
使われ方：AW 余単体の実乗法的な単体的実現。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R]

def convolutionPrecompose {H K : Comon (Complex R)} (f : H ⟶ K) (B : Mon (Complex R)) :
    (convolutionFunctor R K).obj B ⟶ (convolutionFunctor R H).obj B :=
  Mon.Hom.mk' ((MonoidalClosed.pre f.hom).app B.X)
    (convolutionPrecompose_one R f B) (convolutionPrecompose_mul R f B)

lemma convolutionPrecompose_hom {H K : Comon (Complex R)} (f : H ⟶ K)
    (B : Mon (Complex R)) :
    (convolutionPrecompose R f B).hom = (MonoidalClosed.pre f.hom).app B.X := rfl

def convolutionPrecomposeNatTrans {H K : Comon (Complex R)} (f : H ⟶ K) :
    convolutionFunctor R K ⟶ convolutionFunctor R H where
  app := convolutionPrecompose R f
  naturality _ _ g := by
    apply Mon.Hom.ext'
    exact (MonoidalClosed.pre f.hom).naturality g.hom

def convolutionContravariant (B : Mon (Complex R)) :
    (Comon (Complex R))ᵒᵖ ⥤ Mon (Complex R) where
  obj H := (convolutionFunctor R H.unop).obj B
  map f := convolutionPrecompose R f.unop B
  map_id H := by
    apply Mon.Hom.ext'
    change (MonoidalClosed.pre (𝟙 H.unop.X)).app B.X = 𝟙 _
    rw [MonoidalClosed.pre_id]
    rfl
  map_comp f g := by
    apply Mon.Hom.ext'
    change (MonoidalClosed.pre (g.unop.hom ≫ f.unop.hom)).app B.X =
      (MonoidalClosed.pre f.unop.hom).app B.X ≫ (MonoidalClosed.pre g.unop.hom).app B.X
    rw [MonoidalClosed.pre_map]
    rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
