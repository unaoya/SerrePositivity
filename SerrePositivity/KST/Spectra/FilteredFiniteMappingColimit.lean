module

public import SerrePositivity.KST.Spectra.FilteredFiniteMapping
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
概要：有限な点つき源からの内部 Hom は filtered colimit を保存する。
方針：各単体次数で代表の因子分解と等式の後続段での実現を使う。
規約：Kan 性は不要。基点条件も保つ内部 Hom の主張。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。loop と telescope の可換性。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory SSet

namespace SerrePositivity.KST.Spectra.PointedMapping

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {J : Type u} [SmallCategory J] [IsFiltered J]
  {D : J ⥤ PointedSimplicialSet.{u}} {c : Cocone D}
  (hc : IsColimit (PointedSimplicialSet.forget.mapCocone c))
  (A : PointedSimplicialSet.{u}) [A.right.Finite]

include hc in
/-- 概要：有限な点つき源からの Hom を filtered cocone へ施すと基礎単体集合の余極限。
方針：各次数の単体を Yoneda の同値で写像族に移し、型の余極限を判定する。
規約：基礎単体集合の cocone の余極限性を入力する。
使われ方：Goerss–Jardine I §7、HTT A.3.3。有限な内部 Hom の余極限保存。 -/
def finite_basedHom_isColimit :
    IsColimit ((PointedObject.basedHomFunctor A ⋙ PointedSimplicialSet.forget).mapCocone c) := by
  apply evaluationJointlyReflectsColimits
  rintro ⟨n⟩
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro x
    change (PointedObject.basedHom A c.pt).right.obj (Opposite.op n) at x
    obtain ⟨j, t, ht⟩ := finite_basedHom_factorization hc A (SSet.yonedaEquiv.symm x)
    refine ⟨j, SSet.yonedaEquiv t, ?_⟩
    change x = (PointedObject.basedHomMap (Y := D.obj j) (Z := c.pt) A
      (c.ι.app j)).right.app (Opposite.op n) (SSet.yonedaEquiv t)
    apply SSet.yonedaEquiv.symm.injective
    rw [← SSet.yonedaEquiv_symm_comp, Equiv.symm_apply_apply]
    exact ht.symm
  · intro j x y h
    change (PointedObject.basedHom A (D.obj j)).right.obj (Opposite.op n) at x y
    change (PointedObject.basedHomMap (Y := D.obj j) (Z := c.pt) A
      (c.ι.app j)).right.app (Opposite.op n) x =
      (PointedObject.basedHomMap (Y := D.obj j) (Z := c.pt) A
        (c.ι.app j)).right.app (Opposite.op n) y at h
    have h' : SSet.yonedaEquiv.symm x ≫
        (PointedObject.basedHomMap (Y := D.obj j) (Z := c.pt) A (c.ι.app j)).right =
      SSet.yonedaEquiv.symm y ≫
        (PointedObject.basedHomMap (Y := D.obj j) (Z := c.pt) A (c.ι.app j)).right := by
      rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp, h]
    obtain ⟨k, v, hv⟩ := finite_basedHom_eq_eventually hc A j
      (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm y) h'
    refine ⟨k, v, ?_⟩
    change (PointedObject.basedHomMap A (D.map v)).right.app (Opposite.op n) x =
      (PointedObject.basedHomMap A (D.map v)).right.app (Opposite.op n) y
    apply SSet.yonedaEquiv.symm.injective
    rw [← SSet.yonedaEquiv_symm_comp, ← SSet.yonedaEquiv_symm_comp]
    exact hv

/-- 概要：有限な点つき源からの内部 Hom は点つき filtered colimit を保存する。
方針：単体次数ごとの余極限を証明し、基点忘却の同型反映で点つき圏へ戻す。
規約：源・標的の Kan 性は要求しない。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。loop と filtered colimit の比較。 -/
instance finite_basedHom_preservesColimit (D : J ⥤ PointedSimplicialSet.{u}) :
    PreservesColimit D (PointedObject.basedHomFunctor A) := by
  constructor
  intro c hc
  constructor
  let : ReflectsColimit (D ⋙ PointedObject.basedHomFunctor A) PointedSimplicialSet.forget :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  apply isColimitOfReflects PointedSimplicialSet.forget
  exact finite_basedHom_isColimit (hc := isColimitOfPreserves PointedSimplicialSet.forget hc) A

end

end SerrePositivity.KST.Spectra.PointedMapping
