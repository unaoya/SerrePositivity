module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoClassLayerIsos
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroUnderlyingMaps

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorClassLayerMaps

/-!
概要：二切断候補の係数模型射と準同型 zigzag の H⁻² 作用を元の実係数で計算する。
方針：各実 cospan 射の対角二成分を、元の層ホモロジー自然性へ渡す。
規約：共通源の消滅は構成済み。使われ方：実 roof 候補の π₂ 係数の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

lemma sourceToImage_layer : homologyMap (d.sourceToImage R).hom (-2) ≫ (d.imageLayerIso R).hom =
    (d.sourceLayerIso R).hom ≫ homologyMap (d.classCoefficient R).hom (-3) :=
  PostnikovSuccessorClassInverseData.sourceToImage_layer
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma imageToPath_layer : homologyMap (d.imageToPath R).hom (-2) ≫ (d.pathLayerIso R).hom =
    (d.imageLayerIso R).hom :=
  PostnikovSuccessorClassInverseData.imageToPath_layer
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma targetToPath_layer : homologyMap (d.targetToPath R).hom (-2) ≫ (d.pathLayerIso R).hom =
    (d.targetComposedLayerIso R).hom :=
  PostnikovSuccessorClassInverseData.targetToPath_layer
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma targetToStandard_layer : homologyMap (d.targetToStandard R).hom (-2) ≫
    (d.targetLayerIso R).hom = (d.targetComposedLayerIso R).hom :=
  PostnikovSuccessorClassInverseData.targetToStandard_layer
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
