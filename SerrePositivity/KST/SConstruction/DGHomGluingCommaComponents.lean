module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CommaPrimitiveActions
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.PrimitiveComparison

/-! # 元の gluing 三成分と同じ comma 表示の斉次回収
概要：元の左右成分と第三成分を、構成済みの実 Hom 同型で厳密に回収する。
方針：元の鎖射影と Yoneda 同型の成分公式を評価する。
規約：実合成と全次数を保持。使われ方：cone Hom 写像の合成保存。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)

/-- 同じ Hom 同型を通した第三成分は元の第三成分の Yoneda 逆像。 -/
lemma dgHomGluingCommaPrimitive_element {i j : ℤ} (hij : i + (-1) = j)
    (a : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y).X i) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R D (RightModule R C) M.toFunctor
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y)).v i j hij
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M X Y).hom.f i a) =
      (dgYonedaIso R X.left (M.rightAt Y.right)).inv.f j
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D M X Y).v i j hij a) :=
  ConcreteCategory.congr_hom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso_primitive_v R C D M X Y i j hij) a

/-- 同じ第三成分を元の Yoneda 評価で戻すと元の比較成分を回収する。 -/
lemma dgHomGluingPrimitive_recover {i j : ℤ} (hij : i + (-1) = j)
    (a : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y).X i) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D M X Y).v i j hij a =
      (dgYonedaIso R X.left (M.rightAt Y.right)).hom.f j
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R D (RightModule R C) M.toFunctor
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y)).v i j hij
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M X Y).hom.f i a)) := by
  rw [dgHomGluingCommaPrimitive_element]
  have he := ConcreteCategory.congr_hom
    (congrArg (fun f => f.f j) (dgYonedaIso R X.left (M.rightAt Y.right)).inv_hom_id)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D M X Y).v i j hij a)
  exact he.symm

/-- 元の左射影の comma 表示は、同じ左成分の Yoneda 像。 -/
lemma dgHomGluingCommaLeft_element (i : ℤ)
    (a : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y).X i) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R D (RightModule R C) M.toFunctor
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y)).f i
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M X Y).hom.f i a) =
      (yonedaHom R C X.left Y.left).f i ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y).f i a) :=
  ConcreteCategory.congr_hom
    (congrArg (fun f => f.f i) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso_left R C D M X Y)) a

/-- 元の右射影の comma image は、同じ右成分の元の双加群関手像。 -/
lemma dgHomGluingCommaImage_element (i : ℤ)
    (a : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y).X i) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R D (RightModule R C) M.toFunctor
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y)).f i
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M X Y).hom.f i a) =
      (M.toFunctor.map X.right Y.right).f i ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M X Y).f i a) := by
  have he := ConcreteCategory.congr_hom
    (congrArg (fun f => f.f i) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso_right R C D M X Y)) a
  change (M.toFunctor.map X.right Y.right).f i
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R D (RightModule R C) M.toFunctor
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y)).f i
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M X Y).hom.f i a)) = _
  exact congrArg (fun t => (M.toFunctor.map X.right Y.right).f i t) he

end SerrePositivity.KST.SConstruction
