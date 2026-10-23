module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightDirectSourcePath
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightDenCoefficientRestore
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathImageWhisker

/-!
概要：元の直接 class 模型射の経路を復元すると、元の source 自然性の class 像に一致する。
方針：指定直接経路の全射式と係数復元三角形を、元の Path.map の合成則で繋ぐ。
規約：端点だけでなく全 class 経路を同定。使われ方：模型の source 経路の実適用。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

lemma fixedRightDirectWitness_restore : (d.fixedRightDirectWitness R).hom ≫
    Path.map R (d.rightDenominatorClassRestore R) =
    (d.fixedRightDirectSourcePath R).hom ≫
      Path.map R (postnikovPerturbedClass R (B.obj j).obj 1 (by omega)) := by
  let e := postnikovCommonRightImageToSecond R f d.baseInverse d.layerInverse
  let v := postnikovCellImageRelative R (B.obj d.layerInverse.zero.stage).obj (B.obj j).obj
    (d.classBase R) 1 (by omega) (d.lowerBaseInverse R).roof.denominator
    (postnikovCommonRightDenDirectMap R f d.baseInverse d.layerInverse d.target_le)
  let k := postnikovCommonRightDenDirectToZero R f d.baseInverse d.layerInverse d.target_le
  let r := d.rightDenominatorClassRestore R
  let h₀ := (d.fixedRightDirectWitness_hom R).trans
    ((postnikovCommonRightDenDirectContourPath_hom R f d.baseInverse d.layerInverse
      d.target_le).trans
      (postnikovCommonRightDenDirectPath_hom R f d.baseInverse d.layerInverse d.target_le))
  let h₁ := congrArg (fun t => t ≫ Path.map R r) h₀
  let h₂ := Path.map_post_whisker R e v.hom k r
  let h₃ := congrArg (fun t => e ≫ (v.hom ≫ Path.map R t))
    (d.rightDenominatorClassRestore_triangle R)
  let h₄ := congrArg (fun t => e ≫ t)
    (postnikovCellImageRelative_map R (B.obj d.layerInverse.zero.stage).obj (B.obj j).obj
      (d.classBase R) 1 (by omega) (d.lowerBaseInverse R).roof.denominator
      (postnikovCommonRightDenDirectMap R f d.baseInverse d.layerInverse d.target_le))
  exact (((h₁.trans h₂).trans h₃).trans h₄).trans (d.fixedRightDirectSourcePath_class R).symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
