module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorMixedHom

/-!
概要：標的の豊穣単位における相対 Hom の混合作用。
方針：後合成の単位を消去し、内部 Hom の恒等射の後合成を curry' の式で計算する。
規約：定義域の底上の射は任意。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、固定した fibration での対角評価の値の計算。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：標的の恒等射における混合作用は定義域の前合成の通常の射を表す。
方針：豊穣後合成の単位則と curry' の後合成の式を使う。
規約：底や射影の充填性は不要。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、対角 coherent 図式を通常の図式へ戻す。 -/
lemma relativeFunctorMixedHom_unit {B : SSet.{u}} {a b : Over B} (f : a ⟶ b) (p : Over B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorIdentity p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorMixedHom f p p =
      curry' (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p.hom f) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorMixedHom, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorPostHom_id,
    ← curry'_id, curry'_ihom_map, Category.id_comp]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
