module

public import SerrePositivity.InfinityCategories.F2.Ind.DensityFiberTransformationFamily
public import SerrePositivity.InfinityCategories.F2.Ind.IntervalYonedaEvaluation

/-!
概要：元の comma 比較の指定値写像を、大域密度変換の同じ fiber 上の評価へ比較する。
方針：全 fiber 上の区間作用の同型を、元の interval Yoneda 評価で後合成する。
規約：同じ native 余錐の作用と同じ大域変換を使う。
使われ方：恒等点復元射上の大域評価との比較を、元の comma 比較へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)

/-- 元の大域密度変換の区間作用を、元の恒等点で評価した全 fiber の値写像。 -/
def presheafDensityOriginalFiberYonedaValue :=
  presheafDensityOriginalFiberInterval F x ≫ intervalYonedaEvaluation F x

/-- 元の comma の指定値写像は、同じ区間作用を同じ恒等点で評価したもの。 -/
lemma presheafElementsYonedaSliceValue_interval :
    presheafElementsYonedaSliceValue F x =
      presheafElementsYonedaSliceInterval F x ≫ intervalYonedaEvaluation F x := by
  rw [presheafElementsYonedaSliceValue, yonedaPresheafEvaluation_interval]
  rfl

/-- 元の comma の実際の値写像と元の大域変換の値写像を、同じ全 fiber 上で比較する。 -/
def presheafDensityFiberYonedaValueIso :
    FunctorIso (presheafElementsYonedaSliceValue F x)
      (presheafDensityOriginalFiberYonedaValue F x) := by
  rw [presheafElementsYonedaSliceValue_interval]
  exact FunctorIso.postcomp (presheafDensityFiberIntervalIso F x) (intervalYonedaEvaluation F x)

end SerrePositivity.InfinityCategories.F2.Ind
