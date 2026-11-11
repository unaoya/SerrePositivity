module
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomHEqAlgebra

/-!
概要：端点と次数を等号で比較した全 Hom の異種等号は、閉零射による後合成を保つ。
方針：元の対象・次数の等号を消去して、射と係数の等号へ戻す。
規約：元の全次数係数と実閉射を保持する。
使われ方：bar の面の端点輸送を、元の余積包含の後合成まで通す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma dgModuleHomClosedPost_heq {M N P M' N' P' : ModuleCategory R D} {k l : ℤ}
    (hM : M = M') (hN : N = N') (hP : P = P') (hk : k = l)
    (i : N ⟶ P) (i' : N' ⟶ P') (hi : HEq i i')
    (f : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) N)).X k)
    (f' : (moduleHom R D (ForgetEnrichment.to (Complex R) M')
      (ForgetEnrichment.to (Complex R) N')).X l) (hf : HEq f f') :
    HEq ((eHomWhiskerLeft (Complex R) M i).f k f)
      ((eHomWhiskerLeft (Complex R) M' i').f l f') := by
  cases hM
  cases hN
  cases hP
  cases hk
  cases eq_of_heq hi
  cases eq_of_heq hf
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
