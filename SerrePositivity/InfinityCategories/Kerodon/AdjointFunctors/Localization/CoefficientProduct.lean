module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.NerveProduct

/-!
# 元の二つの Cat 値係数の積

概要：同じ底の全作用素で元の二つの係数を成分ごとに組にする。
方針：元の積関手の厳密な恒等・合成則を使う。
規約：係数の元の全対象・全縦射を保持する。
使われ方：混合二方向の元の hammock graph の分解。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.CoefficientProduct
open CategoryTheory
variable {B : Type v} [Category.{w} B]
def diagram (P Q : B ⥤ Cat.{u, u}) : B ⥤ Cat.{u, u} where
  obj b := Cat.of (P.obj b × Q.obj b)
  map f := ((P.map f).toFunctor.prod (Q.map f).toFunctor).toCatHom
  map_id b := by
    apply Cat.Hom.ext
    change ((P.map (𝟙 b)).toFunctor.prod (Q.map (𝟙 b)).toFunctor) = 𝟭 _
    rw [P.map_id, Q.map_id]
    rfl
  map_comp f g := by
    apply Cat.Hom.ext
    change ((P.map (f ≫ g)).toFunctor.prod (Q.map (f ≫ g)).toFunctor) = _
    rw [P.map_comp, Q.map_comp]
    rfl
def point : B ⥤ Cat.{u, u} := (Functor.const B).obj (Cat.of (Discrete PUnit.{u + 1}))
lemma pair_heq {A A' B B' : Type u} {a : A} {a' : A'} {b : B} {b' : B'}
    (ha : HEq a a') (hb : HEq b b') : HEq (a, b) (a', b') := by
  cases ha
  cases hb
  rfl
lemma pointHom_heq {x y x' y' : Discrete PUnit.{u + 1}} (f : x ⟶ y) (g : x' ⟶ y') :
    HEq f g := by
  have hx : x = x' := Subsingleton.elim _ _
  have hy : y = y' := Subsingleton.elim _ _
  cases hx
  cases hy
  exact heq_of_eq (Subsingleton.elim _ _)
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.CoefficientProduct
