module
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedHomNaturality
public import SerrePositivity.DifferentialGraded.Endomorphism.LocalizationHomNaturality

/-! # 指定ホモトピー射影的加群による主導来tensor–Hom随伴

解像度で構成した射集合同値の自然性を局所化の全射へ拡張する。
compact生成性やMorita同値はここでは仮定せず、結論も随伴まで。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)
variable (hE : moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) E))

lemma endomorphismDerivedTensorHomEquiv_naturality_right
    (X : DerivedModuleCategory A (EndomorphismObject E))
    {Y Y' : DerivedModuleCategory A D}
    (φ : (endomorphismDerivedTensor A D E).obj X ⟶ Y) (g : Y ⟶ Y') :
    endomorphismDerivedTensorHomEquiv A D E hE X Y' (φ ≫ g) =
      endomorphismDerivedTensorHomEquiv A D E hE X Y φ ≫
        (endomorphismDerivedHom A D E hE).map g := by
  apply localizationHom_naturality_right (moduleQuasiIso A D)
    (endomorphismDerivedTensor A D E) (endomorphismDerivedHom A D E hE)
    (fun X Y φ => endomorphismDerivedTensorHomEquiv A D E hE X Y φ)
  intro X M M' f φ
  exact endomorphismDerivedTensorHomEquivOnModules_naturality_right A D E hE X.as.obj φ f

lemma endomorphismDerivedTensorHomEquiv_naturality_left
    {X X' : DerivedModuleCategory A (EndomorphismObject E)}
    (f : X ⟶ X') (Y : DerivedModuleCategory A D)
    (φ : (endomorphismDerivedTensor A D E).obj X' ⟶ Y) :
    endomorphismDerivedTensorHomEquiv A D E hE X Y
        ((endomorphismDerivedTensor A D E).map f ≫ φ) =
      f ≫ endomorphismDerivedTensorHomEquiv A D E hE X' Y φ := by
  apply localizationHom_naturality_left (moduleQuasiIso A (EndomorphismObject E))
    (endomorphismDerivedTensor A D E) (endomorphismDerivedHom A D E hE)
    (fun X Y φ => endomorphismDerivedTensorHomEquiv A D E hE X Y φ)
  intro N N' f Y φ
  exact endomorphismDerivedTensorHomEquivOnModules_naturality_left A D E hE Y.as.obj f φ

/-- 射影解像度による再構成導来tensorと導来Homの実際の随伴。 -/
def endomorphismDerivedAdjunction :
    endomorphismDerivedTensor A D E ⊣ endomorphismDerivedHom A D E hE :=
  Adjunction.mkOfHomEquiv
    { homEquiv := endomorphismDerivedTensorHomEquiv A D E hE
      homEquiv_naturality_right := fun φ g =>
        endomorphismDerivedTensorHomEquiv_naturality_right A D E hE _ φ g
      homEquiv_naturality_left_symm := by
        intro X X' Y f g
        apply (endomorphismDerivedTensorHomEquiv A D E hE X Y).injective
        rw [Equiv.apply_symm_apply, endomorphismDerivedTensorHomEquiv_naturality_left,
          Equiv.apply_symm_apply] }

/-- 主導来再構成随伴の単位。 -/
def endomorphismDerivedUnit :
    𝟭 (DerivedModuleCategory A (EndomorphismObject E)) ⟶
      endomorphismDerivedTensor A D E ⋙ endomorphismDerivedHom A D E hE :=
  (endomorphismDerivedAdjunction A D E hE).unit

/-- 主導来再構成随伴の余単位。 -/
def endomorphismDerivedCounit :
    endomorphismDerivedHom A D E hE ⋙ endomorphismDerivedTensor A D E ⟶
      𝟭 (DerivedModuleCategory A D) :=
  (endomorphismDerivedAdjunction A D E hE).counit

lemma endomorphismDerived_left_triangle (X : DerivedModuleCategory A (EndomorphismObject E)) :
    (endomorphismDerivedTensor A D E).map ((endomorphismDerivedUnit A D E hE).app X) ≫
      (endomorphismDerivedCounit A D E hE).app ((endomorphismDerivedTensor A D E).obj X) = 𝟙 _ :=
  (endomorphismDerivedAdjunction A D E hE).left_triangle_components X

lemma endomorphismDerived_right_triangle (Y : DerivedModuleCategory A D) :
    (endomorphismDerivedUnit A D E hE).app ((endomorphismDerivedHom A D E hE).obj Y) ≫
      (endomorphismDerivedHom A D E hE).map ((endomorphismDerivedCounit A D E hE).app Y) = 𝟙 _ :=
  (endomorphismDerivedAdjunction A D E hE).right_triangle_components Y

end SerrePositivity.DifferentialGraded
