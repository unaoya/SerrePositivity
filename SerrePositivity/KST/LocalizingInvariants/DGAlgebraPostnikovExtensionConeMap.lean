module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovExtensionCone
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovFunctor

/-!
概要：Postnikov の cone 複体の射と、元の底への準同型分解の自然性を供給する。
方針：元の層と切断代数の厳密な可換正方形に cone 射を適用する。
規約：複体としての恒等・合成を保持。使われ方：pro 系の非分裂拡大の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CochainComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C D : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] [D.X.IsStrictlyLE 0] (n : ℤ)

lemma postnikovLayerMap_id : postnikovLayerMap R (𝟙 B) n = 𝟙 _ :=
  ((postnikovComplex R (n + 1)) ⋙
    (ComplexShape.embeddingUpIntLE (-(n + 1))).truncLEFunctor (ModuleCat.{u} R)).map_id B

lemma postnikovLayerMap_comp (f : B ⟶ C) (g : C ⟶ D) :
    postnikovLayerMap R (f ≫ g) n = postnikovLayerMap R f n ≫ postnikovLayerMap R g n :=
  ((postnikovComplex R (n + 1)) ⋙
    (ComplexShape.embeddingUpIntLE (-(n + 1))).truncLEFunctor (ModuleCat.{u} R)).map_comp f g

def postnikovExtensionConeMap (f : B ⟶ C) :
    postnikovExtensionCone R B n ⟶ postnikovExtensionCone R C n :=
  mappingCone.map _ _ (postnikovLayerMap R f n) (postnikovMap R f (n + 1)).hom
    (postnikovLayerMap_inclusion R f n).symm

lemma postnikovExtensionConeMap_projection (f : B ⟶ C) :
    postnikovExtensionConeMap R n f ≫ postnikovExtensionConeProjection R C n =
      postnikovExtensionConeProjection R B n ≫ (postnikovMap R f n).hom :=
  cochainConeQuotient_naturality _ _ _ _ _ _ _ _ _ _
    (congrArg Mon.Hom.hom (postnikovTransition_naturality R B f (n + 1) n (by omega))).symm

lemma postnikovExtensionConeMap_id : postnikovExtensionConeMap R n (𝟙 B) = 𝟙 _ := by
  unfold postnikovExtensionConeMap
  have hb : (postnikovMap R (𝟙 B) (n + 1)).hom = 𝟙 _ :=
    (postnikovComplex R (n + 1)).map_id B
  simp only [postnikovLayerMap_id, hb]
  exact mappingCone.map_id _

lemma postnikovExtensionConeMap_comp (f : B ⟶ C) (g : C ⟶ D) :
    postnikovExtensionConeMap R n (f ≫ g) =
      postnikovExtensionConeMap R n f ≫ postnikovExtensionConeMap R n g := by
  unfold postnikovExtensionConeMap
  have hb : (postnikovMap R (f ≫ g) (n + 1)).hom =
      (postnikovMap R f (n + 1)).hom ≫ (postnikovMap R g (n + 1)).hom :=
    (postnikovComplex R (n + 1)).map_comp f g
  simp only [postnikovLayerMap_comp, hb]
  exact mappingCone.map_comp _ _ _ _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
