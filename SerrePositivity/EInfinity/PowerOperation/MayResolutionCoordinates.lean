module

public import SerrePositivity.EInfinity.PowerOperation.MayZeroCoefficient
public import SerrePositivity.EInfinity.PowerOperation.RegularOrbitCoordinates

/-!
# May の指定比較の全係数と境界

May, Definitions 1.2・2.1 の e_s を、同じ W→E(p) によって送った係数。
周期微分のノルムと生成元の差を、実際の BE 係数の境界へ送る。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
variable (p : ℕ) [NeZero p] (k : Type u) [CommRing k]

/-- May の e_s の像。同じ増大付き比較射を全次数で使う。 -/
def mayCoefficientValue (s : ℕ) : (mayArityResolution p k).complex.X s :=
  ((mayResolutionComparison p k).f s).hom (.single 1 1)

lemma mayCoefficientValue_zero :
    mayCoefficientValue p k 0 = mayZeroCoefficientValue p k := rfl

/-- 元の周期解像度の指定微分。 -/
lemma mayResolution_d (s : ℕ) :
    (mayResolution p k).complex.d (s + 1) s =
      if Even (s + 1) then
        (Rep.leftRegular k (MayCyclicGroup.{u} p)).norm.asHom
      else
        (Rep.leftRegular k (MayCyclicGroup.{u} p)).applyAsHom
          (mayCyclicGenerator p) - 𝟙 _ := by
  simp [mayResolution, Rep.FiniteCyclicGroup.resolution,
    Rep.FiniteCyclicGroup.chainComplexFunctor, HomologicalComplex.alternatingConst]

/-- 指定係数の境界は、偶数段でノルム、奇数段で右回転の差。 -/
lemma mayCoefficientValue_boundary (s : ℕ) :
    ((mayArityResolution p k).complex.d (s + 1) s).hom
        (mayCoefficientValue p k (s + 1)) =
      if Even (s + 1) then
        ((mayArityResolution p k).complex.X s).ρ.norm (mayCoefficientValue p k s)
      else
        ((mayArityResolution p k).complex.X s).ρ (mayCyclicGenerator p)
          (mayCoefficientValue p k s) - mayCoefficientValue p k s := by
  have hc := congrArg (fun f => f.hom (.single 1 1))
    ((mayResolutionComparison p k).comm (s + 1) s)
  change _ = _ at hc
  rw [mayResolution_d] at hc
  split_ifs with he
  · rw [ite_eq_left he] at hc
    change _ = Rep.leftRegularHomEquiv _ (_ ≫ _) at hc
    rw [regularHomEvaluation_norm] at hc
    exact hc
  · rw [ite_eq_right he] at hc
    change _ = Rep.leftRegularHomEquiv _ ((_ - 𝟙 _) ≫ _) at hc
    rw [Preadditive.sub_comp, map_sub, regularHomEvaluation_action] at hc
    rw [Category.id_comp] at hc
    exact hc

end SerrePositivity.EInfinity.PowerOperation
