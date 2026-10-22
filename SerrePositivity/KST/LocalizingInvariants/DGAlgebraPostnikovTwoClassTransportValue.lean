module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoClassTransportIso
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraQuasiIsoInverseRoofNaturality

/-!
概要：相対 class 同型から戻した実 roof の値は、元の絶対模型の両脚を保つ。
方針：実同型の両脚の式と、準同型逆 roof の元の脚の自然性を合成する。
規約：全準同型を反転する関手を入力。使われ方：元の候補 roof の class 経路の補正。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)
  {D : Type v} [Category.{w} D] (L : Mon (Complex R) ⥤ D) (hL : InvertsQuasiIsos R L)

lemma classRelativePathRoof_value_left :
    SurjectiveRoof.value R L hL (d.classRelativePathRoof R) ≫
      L.map (HomotopyPullbackModel.left R (d.targetClass R) _) =
        L.map (HomotopyPullbackModel.left R (d.imageClass R) _) := by
  let l : d.imageRelativeModel R ⟶ d.classSource R :=
    SquareZeroExtension.relativeLeft (d.numeratorLayer R) (d.imageClass R)
  have hs : d.imageRelativeComparison R ≫
      HomotopyPullbackModel.left R (d.imageClass R) _ = l :=
    SquareZeroExtension.relativeComparison_left _ _
  have ht : ((d.classRelativeTransportIso R).hom ≫ d.targetRelativeComparison R) ≫
      HomotopyPullbackModel.left R (d.targetClass R) _ = l := by
    rw [Category.assoc, targetRelativeComparison, SquareZeroExtension.relativeComparison_left]
    exact d.classRelativeTransportIso_left R
  have hn := SurjectiveRoof.inverse_value_naturality R (d.imageRelativeComparison R) L
    (d.imageRelativeComparison_quasiIso R) l _ hs hL
  rw [classRelativePathRoof, SurjectiveRoof.postcompose_value, Category.assoc, ← L.map_comp, ht, hn]

lemma classRelativePathRoof_value_right :
    SurjectiveRoof.value R L hL (d.classRelativePathRoof R) ≫
      L.map (HomotopyPullbackModel.right R (d.targetClass R) _) =
        L.map (HomotopyPullbackModel.right R (d.imageClass R) _) := by
  let l : d.imageRelativeModel R ⟶ d.classBase R :=
    SquareZeroExtension.relativeRight (d.numeratorLayer R) (d.imageClass R)
  have hs : d.imageRelativeComparison R ≫
      HomotopyPullbackModel.right R (d.imageClass R) _ = l :=
    SquareZeroExtension.relativeComparison_right _ _
  have ht : ((d.classRelativeTransportIso R).hom ≫ d.targetRelativeComparison R) ≫
      HomotopyPullbackModel.right R (d.targetClass R) _ = l := by
    rw [Category.assoc, targetRelativeComparison, SquareZeroExtension.relativeComparison_right]
    exact d.classRelativeTransportIso_right R
  have hn := SurjectiveRoof.inverse_value_naturality R (d.imageRelativeComparison R) L
    (d.imageRelativeComparison_quasiIso R) l _ hs hL
  rw [classRelativePathRoof, SurjectiveRoof.postcompose_value, Category.assoc, ← L.map_comp, ht, hn]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
