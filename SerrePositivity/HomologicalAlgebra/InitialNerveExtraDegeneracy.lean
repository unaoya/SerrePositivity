module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
import all Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# 始対象を持つ通常の圏の nerve の指定収縮

## 概要
始対象を射列の先頭に前置することで、増大 nerve の extra degeneracy を作る。

## 方針
零面と射列の先頭・尾部による外延性を使う。先頭からの射の一致は始対象性で示す。

## 規約
通常の小圏の元の射列を使い、模型構造や準圏の仮定は置かない。

## 使われ方
Weibel §2.2、HA 1.2.4。bar 重みの各 under 圏の係数付き鎖複体の収縮。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
namespace SerrePositivity.HomologicalAlgebra

/-- 通常の nerve の、型の終対象への同じ増大。 -/
def nerveAugmented (J : Type) [SmallCategory J] : SimplicialObject.Augmented (Type 0) where
  left := nerve J
  right := terminal (Type 0)
  hom := { app _ := terminal.from _ }

/-- 始対象を先頭に置く、元の増大 nerve の指定 extra degeneracy。 -/
def initialNerveExtraDegeneracy {J : Type} [SmallCategory J] (x : J) (hx : IsInitial x) :
    SimplicialObject.Augmented.ExtraDegeneracy (nerveAugmented J) where
  s' := ↾fun _ => ComposableArrows.mk₀ x
  s n := ↾fun s => s.precomp (hx.to s.left)
  s'_comp_ε := terminal.hom_ext _ _
  s₀_comp_δ₁ := by
    ext s
    apply ComposableArrows.ext₀
    rfl
  s_comp_δ₀ n := by
    ext s
    change (s.precomp (hx.to s.left)).δ₀ = s
    rfl
  s_comp_δ n i := by
    ext s
    let t := s.precomp (hx.to s.left)
    have h₀ : ((nerve J).δ i.succ t).obj' 0 = x := by
      change t.obj (i.succ.succAbove 0) = x
      rw [Fin.succAbove_ne_zero_zero i.succ_ne_zero]
      rfl
    have ht : ((nerve J).δ i.succ t).δ₀ = ((nerve J).δ i s) := by
      have h := ConcreteCategory.congr_hom ((nerve J).δ_comp_δ (Fin.zero_le i)) t
      simpa only [types_comp_apply, Fin.castSucc_zero, nerve.δ₀_eq, t,
        ComposableArrows.precomp_δ₀] using h
    apply ComposableArrows.ext_succ h₀ ht
    apply (cancel_epi (eqToHom h₀.symm)).mp
    exact hx.hom_ext _ _
  s_comp_σ n i := by
    ext s
    let t := s.precomp (hx.to s.left)
    have h₀ : ((nerve J).σ i.succ t).obj' 0 = x := by
      change t.obj (i.succ.predAbove 0) = x
      rw [Fin.predAbove_right_zero]
      rfl
    have ht : ((nerve J).σ i.succ t).δ₀ = ((nerve J).σ i s) := by
      have h := ConcreteCategory.congr_hom
        ((nerve J).δ_comp_σ_of_le (Fin.zero_le i.castSucc)) t
      simpa only [types_comp_apply, Fin.castSucc_zero, nerve.δ₀_eq, t,
        ComposableArrows.precomp_δ₀] using h
    apply ComposableArrows.ext_succ h₀ ht
    apply (cancel_epi (eqToHom h₀.symm)).mp
    exact hx.hom_ext _ _

end SerrePositivity.HomologicalAlgebra
