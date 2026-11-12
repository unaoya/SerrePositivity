module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorSpace
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SmallPullback
public import Mathlib.Logic.Small.Basic

/-!
概要：小さい全空間の間の関手空間と相対関手空間は各次数で小さい。
方針：射を次数ごとの写像で符号化し内部 Hom を標準単体からの射で符号化する。
規約：底の小ささや各射の充填性は不要。
使われ方：相対写像空間全体をパラメーターとして collage を分類する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 概要：各次数で小さい単体集合の間の射の型は小さい。
方針：全ての次数の写像の積へ自然変換を単射で入れる。
規約：射の自然性は追加のデータでなく条件。
使われ方：内部 Hom の小ささの入力。 -/
lemma simplicialHom_small_of_small_objects (X Y : SSet.{u + 1})
    [∀ n, Small.{u} (X.obj n)] [∀ n, Small.{u} (Y.obj n)] : Small.{u} (X ⟶ Y) := by
  let code : (X ⟶ Y) → ∀ n, X.obj n → Y.obj n := fun f n x ↦ f.app n x
  apply small_of_injective (f := code)
  intro f g h
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  exact congrFun (congrFun h n) x

/-- 概要：各次数で小さい二つの単体集合の内部 Hom も各次数で小さい。
方針：標準単体からの射を uncurry し小さい射の型へ単射で入れる。
規約：充填性と底の条件は不要。
使われ方：写像空間をパラメーターとする分類。 -/
instance simplicialInternalHom_obj_small (X Y : SSet.{u + 1})
    [∀ n, Small.{u} (X.obj n)] [∀ n, Small.{u} (Y.obj n)] (n : SimplexCategoryᵒᵖ) :
    Small.{u} (((ihom X).obj Y).obj n) := by
  have : ∀ m, Small.{u} ((X ⊗ stdSimplex.obj n.unop).obj m) := by
    intro m
    change Small.{u} (X.obj m × (stdSimplex.obj n.unop).obj m)
    infer_instance
  have := simplicialHom_small_of_small_objects (X ⊗ stdSimplex.obj n.unop) Y
  let code : ((ihom X).obj Y).obj n → (X ⊗ stdSimplex.obj n.unop ⟶ Y) :=
    fun x ↦ uncurry (SSet.yonedaEquiv.symm x)
  apply small_of_injective (f := code)
  intro x y h
  apply SSet.yonedaEquiv.symm.injective
  exact uncurry_injective h

/-- 概要：小さい全空間の相対関手空間は各次数で小さい。
方針：内部 Hom の小ささを fiber の包含の単射性で移す。
規約：固定した底と射影の充填性は不要。
使われ方：普遍的な相対射の族の小さいパラメーター。 -/
instance relativeFunctorSpace_obj_small {A E B : SSet.{u + 1}}
    [∀ n, Small.{u} (A.obj n)] [∀ n, Small.{u} (E.obj n)]
    (p : E ⟶ B) (a : A ⟶ B) (n : SimplexCategoryᵒᵖ) :
    Small.{u} ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a).obj n) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSmall_obj_of_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)) n

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
