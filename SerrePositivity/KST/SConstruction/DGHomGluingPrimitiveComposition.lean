module
public import SerrePositivity.KST.SConstruction.DGHomGluingPrimitiveCommaComposition
public import SerrePositivity.KST.SConstruction.DGHomGluingYonedaActions
public import SerrePositivity.DifferentialGraded.Bimodule.Basic

/-! # 元の gluing 第三成分の全次数合成
概要：元の gluing の実合成の第三成分を、同じ双加群の二作用に戻す。
方針：既存 comma 合成式を同じ Yoneda 同型とその逆像の評価で移す。
規約：全次数の Koszul 符号を保持。使われ方：実 cone Hom の合成保存。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)

private lemma comma_first_eval {p q : ℤ}
    (a : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y).X q)
    (b : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M Y Z).X p) :
    (dgYonedaIso R X.left (M.rightAt Z.right)).hom.f (q + p - 1)
      (forward R (x := representable R X.left) (y := M.rightAt Y.right)
        (z := M.rightAt Z.right) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R D (RightModule R C) M.toFunctor
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y)).v q (q - 1) (by omega)
            ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M X Y).hom.f q a)) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R D
            (RightModule R C) M.toFunctor
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Z)).f p
            ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M Y Z).hom.f p b)) (by omega)) = ((q - 1) *
            p).negOnePow •
      (show (M.value X.left Z.right).X (q + p - 1) from
        leftAction R (M.leftAt X.left) (n := q + p - 1) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M Y Z).f p b)
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D M X Y).v q (q - 1) (by omega) a) (by omega)) := by
  have hA := dgHomGluingCommaPrimitive_element R C D M X Y
    (i := q) (j := q - 1) (by omega) a
  have hB := dgHomGluingCommaImage_element R C D M Y Z p b
  have he := congrArg₂ (fun
      (u : (moduleHom R C (representable R X.left) (M.rightAt Y.right)).X (q - 1))
      (v : (moduleHom R C (M.rightAt Y.right) (M.rightAt Z.right)).X p) =>
    (dgYonedaIso R X.left (M.rightAt Z.right)).hom.f (q + p - 1)
      (forward R (x := representable R X.left) (y := M.rightAt Y.right)
        (z := M.rightAt Z.right) u v (by omega : q - 1 + p = q + p - 1))) hA hB
  exact he.trans (dgHomGluingYoneda_leftAction R C D M X.left Y.right Z.right
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D M X Y).v q (q - 1) (by omega) a) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M Y
      Z).f p b) (by omega))

private lemma comma_second_eval {p q : ℤ}
    (a : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y).X q)
    (b : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M Y Z).X p) :
    (dgYonedaIso R X.left (M.rightAt Z.right)).hom.f (q + p - 1)
      (forward R (x := representable R X.left) (y := representable R Y.left)
        (z := M.rightAt Z.right) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R D (RightModule R C) M.toFunctor
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y)).f q
            ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M X Y).hom.f q a)) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R D
            (RightModule R C) M.toFunctor
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Z)).v p (p - 1) (by omega)
            ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M Y Z).hom.f p b)) (by omega)) = (show (M.value
            X.left Z.right).X (q + p - 1) from
      moduleAction R (M.rightAt Z.right) (x := op Y.left) (y := op X.left)
        (n := q + p - 1) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y).f q a) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D M Y
          Z).v p (p - 1) (by omega) b) (by omega)) := by
  have hA := dgHomGluingCommaLeft_element R C D M X Y q a
  have hB := dgHomGluingCommaPrimitive_element R C D M Y Z
    (i := p) (j := p - 1) (by omega) b
  have he := congrArg₂ (fun
      (u : (moduleHom R C (representable R X.left) (representable R Y.left)).X q)
      (v : (moduleHom R C (representable R Y.left) (M.rightAt Z.right)).X (p - 1)) =>
    (dgYonedaIso R X.left (M.rightAt Z.right)).hom.f (q + p - 1)
      (forward R (x := representable R X.left) (y := representable R Y.left)
        (z := M.rightAt Z.right) u v (by omega : q + (p - 1) = q + p - 1))) hA hB
  exact he.trans (dgHomGluingYoneda_rightAction R C D M X.left Y.left Z.right
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y).f q a) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D M Y Z).v p (p - 1) (by
      omega) b) (by omega))

/-- 元の豊穣合成の第三成分は、二つの元の作用と元の次数符号の和。 -/
lemma dgHomGluingPrimitive_forward {p q : ℤ}
    (a : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y).X q)
    (b : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M Y Z).X p) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D M X Z).v (q + p) (q + p - 1) (by omega)
      (forward R (x := X) (y := Y) (z := Z) a b rfl) =
    ((q - 1) * p).negOnePow •
      (show (M.value X.left Z.right).X (q + p - 1) from
        leftAction R (M.leftAt X.left) (n := q + p - 1) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M Y Z).f p b)
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D M X Y).v q (q - 1) (by omega) a) (by omega)) + q.negOnePow
          • (show (M.value X.left Z.right).X (q + p - 1) from
      moduleAction R (M.rightAt Z.right) (x := op Y.left) (y := op X.left)
        (n := q + p - 1) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y).f q a) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D M Y
          Z).v p (p - 1) (by omega) b) (by omega)) := by
  exact (dgHomGluingPrimitive_forward_comma R C D M X Y Z a b).trans
    (congrArg₂ (fun (u v : (M.value X.left Z.right).X (q + p - 1)) =>
      u + q.negOnePow • v) (comma_first_eval R C D M X Y Z a b)
        (comma_second_eval R C D M X Y Z a b))

end SerrePositivity.KST.SConstruction
