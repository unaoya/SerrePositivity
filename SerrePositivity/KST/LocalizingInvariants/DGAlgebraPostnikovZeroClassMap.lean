module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassZeroTarget
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroLayerFunctor
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroUnderlyingMaps

/-!
概要：零底と shift した実 Postnikov 層の class 標的を、元の代数射に沿って写す。
方針：零底上の層射を shift し、底射と係数射を実平方零代数射へまとめる。
規約：整数 shift と恒等・合成を保持。使われ方：後続段の係数逆による class 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (n s : ℤ) {B C D : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] [D.X.IsStrictlyLE 0]

def postnikovZeroClassMap (f : B ⟶ C) :
    postnikovZeroClassTarget R B n s ⟶ postnikovZeroClassTarget R C n s :=
  SquareZero.mapOver (postnikovMap R f 0)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R B n) s)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R C n) s)
    (DGBimoduleShift.mapOver _ _ s (postnikovLayerZeroMap R f n))

lemma postnikovZeroClassMap_hom (f : B ⟶ C) : (postnikovZeroClassMap R n s f).hom =
    biprod.map (postnikovMap R f 0).hom ((postnikovLayerMap R f n)⟦s⟧') := by
  rw [postnikovZeroClassMap, SquareZero.mapOver_hom, DGBimoduleShift.mapOver_hom]
  rfl

lemma postnikovZeroClassMap_projection (f : B ⟶ C) : postnikovZeroClassMap R n s f ≫
    SquareZero.projection _ _ = SquareZero.projection _ _ ≫ postnikovMap R f 0 :=
  SquareZero.mapOver_projection _ _ _ _

lemma postnikovZeroClassMap_id : postnikovZeroClassMap R n s (𝟙 B) =
    𝟙 (postnikovZeroClassTarget R B n s) := by
  apply Mon.Hom.ext
  rw [postnikovZeroClassMap_hom, postnikovMap_identity, postnikovLayerMap_id]
  change biprod.map (𝟙 (postnikov R B 0).X)
    ((shiftFunctor (Complex R) s).map (𝟙 (postnikovLayer R B n))) = 𝟙 _
  rw [CategoryTheory.Functor.map_id]
  exact cochainBiprodMap_id

lemma postnikovZeroClassMap_comp (f : B ⟶ C) (g : C ⟶ D) :
    postnikovZeroClassMap R n s (f ≫ g) =
      postnikovZeroClassMap R n s f ≫ postnikovZeroClassMap R n s g := by
  apply Mon.Hom.ext
  change (postnikovZeroClassMap R n s (f ≫ g)).hom =
    (postnikovZeroClassMap R n s f).hom ≫ (postnikovZeroClassMap R n s g).hom
  rw [postnikovZeroClassMap_hom, postnikovZeroClassMap_hom, postnikovZeroClassMap_hom,
    postnikovLayerMap_comp]
  have h := congrArg Mon.Hom.hom (postnikovMap_composition R 0 f g)
  rw [h]
  change biprod.map ((postnikovMap R f 0).hom ≫ (postnikovMap R g 0).hom)
    ((shiftFunctor (Complex R) s).map (_ ≫ _)) = _
  rw [CategoryTheory.Functor.map_comp]
  exact (cochainBiprodMap_comp _ _ _ _).symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
