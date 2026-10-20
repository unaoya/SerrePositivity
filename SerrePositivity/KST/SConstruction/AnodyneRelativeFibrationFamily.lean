module
public import SerrePositivity.KST.SConstruction.AnodyneFixedHomotopy

/-! # anodyne 延長の全高次パラメータを保つ fibration 持ち上げ
概要：指定した部分パラメータ族・全基底像・全 anodyne 境界を同時に保って延長する。
方針：anodyne 射と単射の pushout-product の持ち上げ性を使う。
規約：三つの全実写像と共有部分の厳密な一致を入力にし、射影を変更しない。
使われ方：元の三面を保つ消去四面体を、単射源構造射による Hom の制限に沿って選ぶ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial

/-- 部分族・全境界・全基底像を厳密に回収する、全パラメータの anodyne 延長。 -/
lemma exists_anodyneRelativeFibrationFamily {A D P Q E B : SSet.{u}}
    (i : A ⟶ D) (hi : anodyneExtensions i) (j : P ⟶ Q) [Mono j]
    (p : E ⟶ B) [Fibration p]
    (boundary : A ⊗ Q ⟶ E) (part : D ⊗ P ⟶ E) (base : D ⊗ Q ⟶ B)
    (hc : (i ▷ P) ≫ part = (A ◁ j) ≫ boundary)
    (hb : boundary ≫ p = (i ▷ Q) ≫ base)
    (hp : part ≫ p = (D ◁ j) ≫ base) :
    ∃ whole : D ⊗ Q ⟶ E, (D ◁ j) ≫ whole = part ∧
      (i ▷ Q) ≫ whole = boundary ∧ whole ≫ p = base := by
  let pp := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i j
  have : HasLiftingProperty pp.ι p :=
    (anodyneExtensions_pushoutObjObjι' pp hi) p
      ((HomotopicalAlgebra.fibration_iff p).mp inferInstance)
  have hl : pp.inl ≫ pp.ι = D ◁ j := pp.inl_ι
  have hr : pp.inr ≫ pp.ι = i ▷ Q := pp.inr_ι
  let a := pp.isPushout.desc part boundary hc
  have ha : a ≫ p = pp.ι ≫ base := by
    apply pp.isPushout.hom_ext
    · rw [← Category.assoc, pp.isPushout.inl_desc, hp,
        ← Category.assoc, hl]
    · rw [← Category.assoc, pp.isPushout.inr_desc, hb,
        ← Category.assoc, hr]
  let sq : CommSq a pp.ι p base := ⟨ha⟩
  refine ⟨sq.lift, ?_, ?_, sq.fac_right⟩
  · rw [← hl, Category.assoc, sq.fac_left, pp.isPushout.inl_desc]
  · rw [← hr, Category.assoc, sq.fac_left, pp.isPushout.inr_desc]

end SerrePositivity.KST.SConstruction
