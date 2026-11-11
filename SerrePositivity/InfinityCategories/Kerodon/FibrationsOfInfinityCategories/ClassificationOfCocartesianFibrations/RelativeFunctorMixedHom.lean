module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorEnrichedNaturality

/-!
概要：相対 Hom の定義域と標的を同時に動かす豊穣作用。
方針：豊穣後合成の後に底上の前合成を適用し、単位と混合合成を確認する。
規約：定義域の底上の射は反変、標的の豊穣 Hom は共変に作用する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、底の図式と fibration のパラメーターの対角評価。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：底上の定義域の射と豊穣後合成を一つの内部 Hom の射にまとめる。
方針：相対後合成を、定義域を制限する射で後合成する。
規約：f:a→b は b からの関手空間を a からの関手空間へ写す。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、二つの添字を同時に動かす評価。 -/
def relativeFunctorMixedHom {B : SSet.{u}} {a b : Over B} (f : a ⟶ b) (p q : Over B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q.hom p.hom ⟶
      (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p.hom b.hom)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q.hom a.hom) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorPostHom b p q ≫
    (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p.hom b.hom)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre q.hom f)

/-- 概要：両方の添字の恒等射による混合作用は相対関手空間の豊穣単位になる。
方針：前合成の恒等則を消去し、豊穣後合成の単位則へ帰着する。
規約：定義域の恒等は Over 圏の恒等射。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、対角評価の単位則。 -/
lemma relativeFunctorMixedHom_id {B : SSet.{u}} (a p : Over B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorIdentity p ≫ relativeFunctorMixedHom (𝟙 a) p p =
      MonoidalClosed.id (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p.hom a.hom) := by
  rw [relativeFunctorMixedHom, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre_id,
    (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p.hom a.hom)).map_id,
    Category.comp_id, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorPostHom_id]

/-- 概要：二つの定義域の制限と二つの豊穣後合成を同時に合成しても混合作用を保つ。
方針：uncurry して各次数の三つの関手と二つの底上の射を評価する。
規約：定義域の射の合成は g≫f で、豊穣射の合成と逆向きに並ぶ。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、対角評価の豊穣合成則。 -/
lemma relativeFunctorMixedHom_comp {B : SSet.{u}} {a b c : Over B}
    (f : b ⟶ a) (g : c ⟶ b) (p q r : Over B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition p q r ≫ relativeFunctorMixedHom (g ≫ f) p r =
      (relativeFunctorMixedHom f p q ⊗ₘ relativeFunctorMixedHom g q r) ≫
        MonoidalClosed.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p.hom a.hom)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q.hom b.hom) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace r.hom c.hom) := by
  apply uncurry_injective
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, h, k⟩
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro y
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
