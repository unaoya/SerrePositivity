module
public import SerrePositivity.KST.SConstruction.SerreConcreteCubeFunctor
public import Mathlib.CategoryTheory.Limits.Presheaf

/-! # 具体的な立方体圏上の cubical sets
概要：max connection を含む具体的立方体圏上の前層と、その元の立方体を表す Yoneda 射を作る。
方針：宇宙を明示した ulift Yoneda により、任意の大きさの立方体の族を扱う。
規約：余分な connection や座標の反転は加えない。使われ方：鎖関手の余極限による延長。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Opposite

/-- 元の max connection を持つ具体的な立方体圏上の前層。 -/
abbrev CubicalSet := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ ⥤ Type u

/-- 元の立方体を、その射全体からなる表現可能な cubical set へ送る。 -/
def cubicalYoneda : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube ⥤ CubicalSet.{u} := uliftYoneda.{u}

/-- 元の立方体の単体に対応する表現可能前層からの射。 -/
def cubicalCell {K : CubicalSet.{u}} (c : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) (x : K.obj (op c)) :
    (cubicalYoneda.obj c) ⟶ K := uliftYonedaEquiv.symm x

/-- 元の表現可能立方体からの射の全データは、その恒等射での値から回収される。 -/
lemma cubicalCell_equiv {K : CubicalSet.{u}} (c : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube)
    (f : cubicalYoneda.obj c ⟶ K) : cubicalCell c (uliftYonedaEquiv f) = f :=
  uliftYonedaEquiv.symm_apply_apply f

/-- cubical set の射は、元の各立方体の Yoneda 射との合成を保つ。 -/
lemma cubicalCell_naturality {K L : CubicalSet.{u}} (f : K ⟶ L)
    (c : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) (x : K.obj (op c)) :
    cubicalCell c x ≫ f = cubicalCell c (f.app (op c) x) := by
  apply uliftYonedaEquiv.injective
  change f.app (op c) (uliftYonedaEquiv (uliftYonedaEquiv.symm x)) =
    uliftYonedaEquiv (uliftYonedaEquiv.symm (f.app (op c) x))
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end SerrePositivity.KST.SConstruction
