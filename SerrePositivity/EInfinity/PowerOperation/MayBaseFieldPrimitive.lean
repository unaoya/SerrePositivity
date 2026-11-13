module

public import SerrePositivity.EInfinity.PowerOperation.MayCoefficientAction
public import SerrePositivity.EInfinity.PowerOperation.MayNormBaseField

/-!
# 持ち上げた素体にも使える May の指定境界係数

May, Proposition 2.3(ii) の e_{i+1} と T^{p−2}e_{i+1}。
次の段の係数を同じ W→BE 比較で送り、その微分が前の係数のノルムになることを示す。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
variable {k : Type u} [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p]

omit [CharP k p] in
lemma mayBaseFieldDifference_apply_naturality
    {A B : Rep.{u} k (MayCyclicGroup.{u} p)} (f : A ⟶ B)
    (g : MayCyclicGroup.{u} p) (x : A) :
    f.hom ((A.ρ g - 1) x) = (B.ρ g - 1) (f.hom x) := by
  change f.hom (A.ρ g x - x) = B.ρ g (f.hom x) - f.hom x
  rw [map_sub, Rep.hom_comm_apply]

omit [CharP k p] in
/-- 同じ巡回生成元の差の冪は、表現の実射で自然。 -/
lemma mayBaseFieldDifferencePower_naturality
    {A B : Rep.{u} k (MayCyclicGroup.{u} p)} (f : A ⟶ B)
    (g : MayCyclicGroup.{u} p) (m : ℕ) (x : A) :
    f.hom (((A.ρ g - 1) ^ m) x) = ((B.ρ g - 1) ^ m) (f.hom x) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply,
      mayBaseFieldDifference_apply_naturality, ih]

/-- 同じ次の段の係数から、前の係数のノルムを境界に持つ指定元を作る。 -/
def mayBaseFieldAdditivityCoefficient (i : ℕ) : (mayArityResolution p k).complex.X (i + 1) :=
  if Even (i + 1) then mayCoefficientValue p k (i + 1)
  else
    ((((mayArityResolution p k).complex.X (i + 1)).ρ (mayCyclicGenerator p) - 1) ^
      (p - 2)) (mayCoefficientValue p k (i + 1))

/-- 指定した係数の境界は、前の段の同じ係数のノルム。 -/
lemma mayBaseFieldAdditivityCoefficient_boundary (i : ℕ) :
    ((mayArityResolution p k).complex.d (i + 1) i).hom (mayBaseFieldAdditivityCoefficient p i) =
      ((mayArityResolution p k).complex.X i).ρ.norm (mayCoefficientValue p k i) := by
  unfold mayBaseFieldAdditivityCoefficient
  split_ifs with hi
  · rw [mayCoefficientValue_boundary, ite_eq_left hi]
  · rw [mayBaseFieldDifferencePower_naturality, mayCoefficientValue_boundary, ite_eq_right hi]
    change ((((mayArityResolution p k).complex.X i).ρ
      (mayCyclicGenerator p) - 1) ^ (p - 2))
      ((((mayArityResolution p k).complex.X i).ρ (mayCyclicGenerator p) - 1)
        (mayCoefficientValue p k i)) = _
    rw [← Module.End.mul_apply, ← pow_succ]
    have hp : p - 2 + 1 = p - 1 := by
      have h := (Fact.out : p.Prime).two_le
      omega
    rw [hp, ← mayCyclicNorm_baseField p k]

end SerrePositivity.EInfinity.PowerOperation
