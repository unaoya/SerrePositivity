module

public import SerrePositivity.EInfinity.PowerOperation.MayHomogeneousAction
public import Mathlib.Algebra.CharP.Lemmas

/-!
# May の係数作用を実 BE 作用へ送る

May, Definition 2.1 の巡回平衡関係。
同じ入力が巡回作用で不変なら、係数の生成元の差は作用後に消える。
係数を持つ表現は W→BE で使った実部分群への制限そのものである。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open SerrePositivity.EInfinity.BarrattEccles
variable {k : Type u} [CommRing k] (X : (operad k).Algebra)
variable (p : ℕ) [NeZero p] (s : ℕ) (q : ℤ)

/-- 同じ係数表現の元を、元の余鎖複体の次数 −s に読む。 -/
abbrev mayActualCoefficient (c : (mayArityResolution p k).complex.X s) :
    ((operad k).arity p).X (-(s : ℤ)) := c

/-- 同じ比較の境界公式を、元の余鎖複体の微分として読む。 -/
lemma mayActualCoefficient_d (s : ℕ) :
    ((operad k).arity p).d (-((s + 1 : ℕ) : ℤ)) (-(s : ℤ))
      (mayActualCoefficient p (s + 1) (mayCoefficientValue p k (s + 1))) =
    mayActualCoefficient p s
      (if Even (s + 1) then
        ((mayArityResolution p k).complex.X s).ρ.norm (mayCoefficientValue p k s)
      else
        ((mayArityResolution p k).complex.X s).ρ (mayCyclicGenerator p)
          (mayCoefficientValue p k s) - mayCoefficientValue p k s) := by
  exact mayCoefficientValue_boundary p k s

/-- 同じ巡回左作用は、代数の対称列の作用と厳密に一致する。 -/
lemma mayCoefficientAction_eq (g : MayCyclicGroup.{u} p)
    (c : (mayArityResolution p k).complex.X s) :
    mayActualCoefficient p s (((mayArityResolution p k).complex.X s).ρ g c) =
      (((operad k).sequence.map (FiniteBijection.permutation p g.val.down)).f (-(s : ℤ)))
        (mayActualCoefficient p s c) := by
  change (complexRightAction k p g.val.down⁻¹).f (-(s : ℤ)) c = _
  have he : (operad k).sequence.map (FiniteBijection.permutation p g.val.down) =
      complexRightAction k p g.val.down⁻¹ := sequence_map_permutation k p g.val.down
  exact (congrArg (fun f : (operad k).arity p ⟶ (operad k).arity p =>
    f.f (-(s : ℤ)) (mayActualCoefficient p s c)) he).symm

/-- 巡回不変の入力では、係数の各巡回作用が値を変えない。 -/
lemma mayCoefficientAction_invariant (g : MayCyclicGroup.{u} p)
    (c : (mayArityResolution p k).complex.X s) (y : (power X.carrier p).X q)
    (hy : (permutationAction X.carrier p g.val.down).asIso.hom.f q y = y) :
    mayHomogeneousAction X p (-(s : ℤ)) q
      (mayActualCoefficient p s (((mayArityResolution p k).complex.X s).ρ g c)) y =
        mayHomogeneousAction X p (-(s : ℤ)) q (mayActualCoefficient p s c) y := by
  rw [mayCoefficientAction_eq]
  have he := mayHomogeneousAction_equivariance X p g.val.down (-(s : ℤ)) q c y
  rw [hy] at he
  exact he

/-- May の奇数段の係数境界は、巡回不変の入力への作用で零になる。 -/
lemma mayCoefficientAction_sub (g : MayCyclicGroup.{u} p)
    (c : (mayArityResolution p k).complex.X s) (y : (power X.carrier p).X q)
    (hy : (permutationAction X.carrier p g.val.down).asIso.hom.f q y = y) :
    mayHomogeneousAction X p (-(s : ℤ)) q
      (mayActualCoefficient p s (((mayArityResolution p k).complex.X s).ρ g c - c)) y = 0 := by
  change ((mayHomogeneousActionLinear X p (-(s : ℤ)) q).flip y) (_ - _) = 0
  rw [map_sub]
  change mayHomogeneousAction X p (-(s : ℤ)) q
    (mayActualCoefficient p s (((mayArityResolution p k).complex.X s).ρ g c)) y -
    mayHomogeneousAction X p (-(s : ℤ)) q (mayActualCoefficient p s c) y = 0
  rw [mayCoefficientAction_invariant X p s q g c y hy, sub_self]

/-- May の偶数段のノルム係数は、巡回不変入力に対して p 倍として作用する。 -/
lemma mayCoefficientAction_norm
    (c : (mayArityResolution p k).complex.X s) (y : (power X.carrier p).X q)
    (hy : ∀ g : MayCyclicGroup.{u} p,
      (permutationAction X.carrier p g.val.down).asIso.hom.f q y = y) :
    mayHomogeneousAction X p (-(s : ℤ)) q
      (mayActualCoefficient p s (((mayArityResolution p k).complex.X s).ρ.norm c)) y =
        p • mayHomogeneousAction X p (-(s : ℤ)) q (mayActualCoefficient p s c) y := by
  let L := (mayHomogeneousActionLinear X p (-(s : ℤ)) q).flip y
  change L (((mayArityResolution p k).complex.X s).ρ.norm c) = p • L c
  change L ((∑ g : MayCyclicGroup.{u} p,
    ((mayArityResolution p k).complex.X s).ρ g) c) = p • L c
  rw [LinearMap.sum_apply, map_sum]
  have he (g : MayCyclicGroup.{u} p) :
      L (((mayArityResolution p k).complex.X s).ρ g c) = L c :=
    mayCoefficientAction_invariant X p s q g c y (hy g)
  simp only [he, Finset.sum_const, Finset.card_univ, mayCyclicGroup_card]

/-- 標数 p では、指定係数の全ての境界が巡回不変入力への作用で消える。 -/
lemma mayCoefficientAction_boundary_zero [CharP k p]
    (y : (power X.carrier p).X q)
    (hy : ∀ g : MayCyclicGroup.{u} p,
      (permutationAction X.carrier p g.val.down).asIso.hom.f q y = y) :
    mayHomogeneousAction X p (-(s : ℤ)) q
      (((operad k).arity p).d (-((s + 1 : ℕ) : ℤ)) (-(s : ℤ))
        (mayActualCoefficient p (s + 1) (mayCoefficientValue p k (s + 1)))) y = 0 := by
  rw [mayActualCoefficient_d]
  split_ifs with he
  · rw [mayCoefficientAction_norm X p s q _ y hy]
    rw [← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero k p, zero_smul]
  · exact mayCoefficientAction_sub X p s q (mayCyclicGenerator p) _ y (hy _)

end SerrePositivity.EInfinity.PowerOperation
