module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ExtendedTruncationZeroInclusion

/-!
# 元の延長項同型と opposite 比較の同じ一点での整合

概要：同じ延長の一点の逆同型と opposite 比較を合成すると元の opposite 側の項同型になる。
方針：同じ Option 添字を some に固定して元の同型を計算する。
規約：元の extend.XIso・extend.XOpIso を保つ。
使われ方：元の延長切断包含を cycles 包含へ照合する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A]

lemma extendOppositePoint (L : ChainComplex (ModuleCat.{u} A) ℕ) {r : Option ℕ} {n : ℕ}
    (hr : r = some n) :
    (extend.XIso L hr).inv ≫ (extend.XOpIso L r).hom.unop =
      (extend.XIso L.op hr).hom.unop := by
  subst r
  simp [extend.XIso, extend.XOpIso, extend.X]

lemma truncLEIso_inv_point (H : Complex A)
    (e : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ)) [e.IsTruncLE]
    {n : ℕ} {i : ℤ} (hi : e.f n = i) :
    ((H.truncLE' e).extendXIso e hi).inv ≫ (H.truncLEIso e).inv.f i =
      ((H.op.truncGE' e.op).extendXIso e.op hi).hom.unop := by
  change (extend.XIso (H.truncLE' e) (e.r_eq_some hi)).inv ≫
    (extend.XOpIso (H.truncLE' e) (e.r i)).hom.unop = _
  exact _root_.SerrePositivity.ComplexLimits.extendOppositePoint (H.truncLE' e) (e.r_eq_some hi)

end SerrePositivity.ComplexLimits
