module
public import SerrePositivity.KST.SConstruction.DGHomGluingYonedaComposition
public import SerrePositivity.DifferentialGraded.Bimodule.Basic

/-! # 元の Yoneda 同型を通す双加群の二作用
概要：二つの加群合成を、同じ元の双加群の左右作用へ戻す。
方針：全次数の Yoneda 評価と逆像成分の符号を合成する。
規約：符号を消すのは二重交換に限る。使われ方：gluing 第三成分の合成保存。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

/-- 右側の Hom 射を合成すると、元の左作用と元の豊穣合成符号を回収する。 -/
lemma dgHomGluingYoneda_leftAction (x : C) (d d' : D) {r s t : ℤ}
    (a : (M.value x d).X r) (b : GradedHom R d d' s) (ht : r + s = t) :
    (dgYonedaIso R x (M.rightAt d')).hom.f t
      (forward R (x := representable R x) (y := M.rightAt d) (z := M.rightAt d')
        ((dgYonedaIso R x (M.rightAt d)).inv.f r a)
        ((M.toFunctor.map d d').f s b) ht) =
      (r * s).negOnePow • leftAction R (M.leftAt x) b a ht := by
  have he := dgHomGluingYoneda_forward R C x (M.rightAt d) (M.rightAt d')
    ((dgYonedaIso R x (M.rightAt d)).inv.f r a) ((M.toFunctor.map d d').f s b) ht
  erw [dgHomGluingYoneda_inv_hom R C x (M.rightAt d) r a] at he
  exact he

/-- 左の代表 Hom 射との合成では二つの交換符号が消え、元の右作用を回収する。 -/
lemma dgHomGluingYoneda_rightAction (x y : C) (d : D) {r s t : ℤ}
    (a : GradedHom R x y r) (b : (M.value y d).X s) (ht : r + s = t) :
    (dgYonedaIso R x (M.rightAt d)).hom.f t
      (forward R (x := representable R x) (y := representable R y) (z := M.rightAt d)
        ((yonedaHom R C x y).f r a) ((dgYonedaIso R y (M.rightAt d)).inv.f s b) ht) =
      moduleAction R (M.rightAt d) (x := op y) (y := op x) a b (by omega) := by
  erw [dgHomGluingYoneda_forward R C x (representable R y) (M.rightAt d)
    ((yonedaHom R C x y).f r a) ((dgYonedaIso R y (M.rightAt d)).inv.f s b) ht]
  change (r * s).negOnePow •
    (((moduleHomπ R C (representable R y) (M.rightAt d) x).f s
      ((dgYonedaIso R y (M.rightAt d)).inv.f s b)).v r t ht)
      ((dgYonedaIso R x (representable R y)).hom.f r
        ((dgYonedaIso R x (representable R y)).inv.f r a)) = _
  rw [dgHomGluingYoneda_inv_hom R C x (representable R y) r a,
    dgHomGluingYoneda_inv_element R C y x (M.rightAt d) b a ht]
  simp only [smul_smul, mul_comm s r, Int.units_mul_self, one_smul]

end SerrePositivity.KST.SConstruction
