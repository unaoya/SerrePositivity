module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGTensorHom

/-! # 入力とラベルの tensor Hom 作用の合成保存
概要：元の入力とラベルを同時に動かす作用は tensor dg 圏の全次数合成を保持する。
方針：全次数自然性で中間二成分を交換し、それぞれの dg 関手の合成保存を使う。
規約：符号は最初のラベル次数と次の入力次数の積。使われ方：tensor dg 作用。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]

/-- 入力 Hom 作用の全斉次成分の、元のラベル射に関する符号つき自然性。 -/
lemma presentedPerfectDGInputHom_naturality_apply {F G : DGFunctor A D E}
    {X Y : PresentedPerfectDGObject A D} {p q n : ℤ}
    (a : GradedHom A F G p) (b : GradedHom A X Y q) (hn : p + q = n) :
    (p * q).negOnePow • forward A (((presentedPerfectDGAction A D E F).map X Y).f q b)
        ((presentedPerfectDGInputHom A D E F G Y).f p a) (by omega) =
      forward A ((presentedPerfectDGInputHom A D E F G X).f p a)
        (((presentedPerfectDGAction A D E G).map X Y).f q b) hn :=
  dgFunctorFamilyNaturality_apply A (PresentedPerfectDGObject A D) (PresentedPerfectDGObject A E)
    (presentedPerfectDGInputHom A D E F G)
    (presentedPerfectDGInputHom_naturality A D E F G) a b hn

/-- 四つの元の斉次成分について、作用は交差符号を保って合成と交換する。 -/
lemma presentedPerfectDGTensorHom_interchange
    {F G H : DGFunctor A D E} {X Y Z : PresentedPerfectDGObject A D} {p q r s n : ℤ}
    (a : GradedHom A F G p) (b : GradedHom A X Y q)
    (c : GradedHom A G H r) (d : GradedHom A Y Z s)
    (hn : (p + q) + (r + s) = n) :
    forward A
        (forward A ((presentedPerfectDGInputHom A D E F G X).f p a)
          (((presentedPerfectDGAction A D E G).map X Y).f q b) rfl)
        (forward A ((presentedPerfectDGInputHom A D E G H Y).f r c)
          (((presentedPerfectDGAction A D E H).map Y Z).f s d) rfl) hn =
      (q * r).negOnePow •
        forward A ((presentedPerfectDGInputHom A D E F H X).f (p + r) (forward A a c rfl))
          (((presentedPerfectDGAction A D E H).map X Z).f (q + s) (forward A b d rfl))
          (by omega) := by
  have hc := presentedPerfectDGInputHom_naturality_apply A D E c b
    (n := q + r) (by omega)
  have hc' := congrArg (fun z => (r * q).negOnePow • z) hc
  simp only [smul_smul, Int.units_mul_self, one_smul] at hc'
  rw [mul_comm r q] at hc'
  have h := dgMiddleInterchange (A := A) (E := PresentedPerfectDGObject A E)
    ((presentedPerfectDGInputHom A D E F G X).f p a)
    (((presentedPerfectDGAction A D E G).map X Y).f q b)
    ((presentedPerfectDGInputHom A D E G H Y).f r c)
    (((presentedPerfectDGAction A D E H).map Y Z).f s d)
    ((presentedPerfectDGInputHom A D E G H X).f r c)
    (((presentedPerfectDGAction A D E H).map X Y).f q b) _ hc' hn
  have hL := DGFunctor.map_forward A (presentedPerfectDGLabelAction A D E X) a c rfl
  have hR := DGFunctor.map_forward A (presentedPerfectDGAction A D E H) b d rfl
  simp only [presentedPerfectDGLabelAction_map] at hL
  erw [← hL, ← hR] at h
  exact h

local instance tensorActionSourceEnrichment :
    DGCategory A (DGTensorCategory A (DGFunctor A D E) (PresentedPerfectDGObject A D)) :=
  dgTensorEnrichment A (DGFunctor A D E) (PresentedPerfectDGObject A D)

/-- 元の tensor Hom 作用は、元の tensor dg 圏の豊穣合成を厳密に保持する。 -/
lemma presentedPerfectDGTensorHom_composition
    (x y z : DGTensorCategory A (DGFunctor A D E) (PresentedPerfectDGObject A D)) :
    eComp (Complex A) x y z ≫ presentedPerfectDGTensorHom A D E x.1 z.1 x.2 z.2 =
      (presentedPerfectDGTensorHom A D E x.1 y.1 x.2 y.2 ⊗ₘ
        presentedPerfectDGTensorHom A D E y.1 z.1 y.2 z.2) ≫
          eComp (Complex A) ((presentedPerfectDGAction A D E x.1).obj x.2)
            ((presentedPerfectDGAction A D E y.1).obj y.2)
            ((presentedPerfectDGAction A D E z.1).obj z.2) := by
  apply dgTensorComposition_of_elements x y z
  intro p q r s n hn a b c d
  have hf := congrArg (fun t => (presentedPerfectDGTensorHom A D E x.1 z.1 x.2 z.2).f n t)
    (dgTensor_forward A (x := x) (y := y) (z := z) a b c d hn)
  simp only [Units.smul_def, map_zsmul] at hf
  have hm := presentedPerfectDGTensorHom_apply A D E (forward A a c rfl)
    (forward A b d rfl) (n := n) (by omega)
  have ha := presentedPerfectDGTensorHom_apply A D E a b rfl
  have hb := presentedPerfectDGTensorHom_apply A D E c d rfl
  have hr := congrArg₂ (fun a b => forward A (D := PresentedPerfectDGObject A E)
    (x := (presentedPerfectDGAction A D E x.1).obj x.2)
    (y := (presentedPerfectDGAction A D E y.1).obj y.2)
    (z := (presentedPerfectDGAction A D E z.1).obj z.2) a b hn) ha hb
  have hm' := congrArg (fun t => (q * r).negOnePow • t) hm
  simp only [Units.smul_def] at hm'
  exact hf.trans (hm'.trans
    ((presentedPerfectDGTensorHom_interchange A D E a b c d hn).symm.trans hr.symm))

end SerrePositivity.KST.SConstruction
