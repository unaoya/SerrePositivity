module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassCompatibility

/-!
概要：標準 class に整合した新しい係数逆が、元の層の左右三角形を満たすことを示す。
方針：同じ実逆 d の三角形と A の遷移の自然性を、元の整数 shift で写す。
規約：class 経路で使った係数を取り替えない。使われ方：元の二切断射の実逆。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

lemma postnikovCommonClassCompatibilityCoefficient_hom :
    (postnikovCommonClassCompatibilityCoefficient R f c d (hj := hj)).hom =
      d.coefficient.hom⟦(1 : ℤ)⟧' ≫
        (postnikovLayerMap R (A.transition hj).hom 1)⟦(1 : ℤ)⟧' := by
  rw [postnikovCommonClassCompatibilityCoefficient, Bimod.comp_hom',
    postnikovCommonShiftedCoefficientMap_hom, postnikovCommonClassTransitionCoefficient,
    postnikovCellClassOverCoefficient_hom]

lemma postnikovCommonClassCompatibilityCoefficient_left :
    (postnikovLayerMap R (f.app d.zero.stage).hom 1)⟦(1 : ℤ)⟧' ≫
      (postnikovCommonClassCompatibilityCoefficient R f c d (hj := hj)).hom =
        (postnikovLayerMap R
          (A.transition (hj.trans (d.zero.inverse_le.trans d.zero.stage_le))).hom 1)⟦(1 : ℤ)⟧' := by
  have h : postnikovLayerMap R (f.app d.zero.stage).hom 1 ≫
      (d.coefficient.hom ≫ postnikovLayerMap R (A.transition hj).hom 1) =
    postnikovLayerMap R
      (A.transition (hj.trans (d.zero.inverse_le.trans d.zero.stage_le))).hom 1 := by
    rw [← Category.assoc, d.left_coefficient, ← postnikovLayerMap_comp]
    exact congrArg (fun t => postnikovLayerMap R t 1)
      (congrArg (fun t => t.hom)
        (A.transition_comp (d.zero.inverse_le.trans d.zero.stage_le) hj))
  rw [postnikovCommonClassCompatibilityCoefficient_hom,
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, h]

lemma postnikovCommonClassCompatibilityCoefficient_right :
    (postnikovCommonClassCompatibilityCoefficient R f c d (hj := hj)).hom ≫
      (postnikovLayerMap R (f.app j).hom 1)⟦(1 : ℤ)⟧' =
        (postnikovLayerMap R
          (B.transition (hj.trans (d.zero.inverse_le.trans d.zero.stage_le))).hom 1)⟦(1 : ℤ)⟧' := by
  have hn : postnikovLayerMap R (A.transition hj).hom 1 ≫
      postnikovLayerMap R (f.app j).hom 1 = postnikovLayerMap R (f.app i).hom 1 ≫
        postnikovLayerMap R (B.transition hj).hom 1 :=
    (f.map (postnikovLayerFunctor R 1)).naturality hj
  have h : (d.coefficient.hom ≫ postnikovLayerMap R (A.transition hj).hom 1) ≫
      postnikovLayerMap R (f.app j).hom 1 = postnikovLayerMap R
        (B.transition (hj.trans (d.zero.inverse_le.trans d.zero.stage_le))).hom 1 := by
    rw [Category.assoc, hn, ← Category.assoc, d.right_coefficient, ← postnikovLayerMap_comp]
    exact congrArg (fun t => postnikovLayerMap R t 1)
      (congrArg (fun t => t.hom)
        (B.transition_comp (d.zero.inverse_le.trans d.zero.stage_le) hj))
  rw [postnikovCommonClassCompatibilityCoefficient_hom,
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, h]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
