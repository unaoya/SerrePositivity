module
public import SerrePositivity.DifferentialGraded.Tensor.Triple
public import SerrePositivity.DifferentialGraded.Bimodule.Value

/-! # 対角双加群の左右単位の一致
概要：元の対角双加群の左右 tensor 単位が同じ実同型であることを示す。
方針：Yoneda 作用と代表加群の作用を全次数で比較し、balanced tensor の普遍性を使う。
規約：Koszul 符号と因子の順を保持する。使われ方：graph の右恒等入力の整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 対角の左作用と代表加群の右作用は、同じ順の全 Hom tensor 上で一致する。 -/
lemma dgDiagonal_leftAction_eq_rightAction (b x c : D) :
    BalancedTensor.leftAction A D ((Bimodule.diagonal A D).leftAt b) x c =
      BalancedTensor.rightAction A D (representable A c) b x := by
  apply tensorHom_ext
  intro p q n hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro h
  have hl := BalancedTensor.leftAction_apply A D ((Bimodule.diagonal A D).leftAt b)
    x c p q n hn f h
  have hr := BalancedTensor.rightAction_apply A D (representable A c) b x p q n hn f h
  refine hl.trans (Eq.trans ?_ hr.symm)
  change (((moduleHomπ A D (representable A x) (representable A c) b).f p
      ((yonedaHom A D x c).f p f)).v q n (by omega)) h =
    (p * q).negOnePow • forward A h f (by omega)
  exact yonedaHom_element A D x c b f h (by omega)

/-- 対角双加群の左右単位は、各元の値の複体で同じ chain map。 -/
lemma dgDiagonal_rightUnitValue_eq_leftUnit (b c : D) :
    (BimoduleTensor.rightUnitValueIso A D D (Bimodule.diagonal A D) b c).hom =
      (BimoduleTensor.leftUnitValueIso A D D (Bimodule.diagonal A D) b c).hom := by
  apply BalancedTensor.hom_ext
  intro x
  change BalancedTensor.ι A D (representable A c) ((Bimodule.diagonal A D).leftAt b) x ≫
      BalancedTensor.yonedaEvaluation A D c ((Bimodule.diagonal A D).leftAt b) = _
  rw [BalancedTensor.ι_yonedaEvaluation]
  exact (dgDiagonal_leftAction_eq_rightAction A D b x c).trans
    (BimoduleTensor.ι_leftUnitValueIso_hom A D D (Bimodule.diagonal A D) b x c).symm

/-- 元の対角双加群の左右単位は、全 Hom 自然な実同型として一致する。 -/
lemma dgDiagonal_rightUnitIso_eq_leftUnit :
    BimoduleTensor.rightBimoduleUnitIso A D D (Bimodule.diagonal A D) =
      BimoduleTensor.leftBimoduleUnitIso A D D (Bimodule.diagonal A D) := by
  apply Iso.ext
  apply BimoduleCategory.value_hom_ext
  intro b c
  rw [BimoduleTensor.rightBimoduleUnitIso_hom_value,
    BimoduleTensor.leftBimoduleUnitIso_hom_value]
  exact dgDiagonal_rightUnitValue_eq_leftUnit A D b c

end SerrePositivity.KST.SConstruction
