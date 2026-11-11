module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctor
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorPostLaws

/-!
概要：相対関手空間の宇宙移送と底上の前合成・後合成の整合性。
方針：内部 Hom のパラメーターと入力ごとに持ち上げの計算を比較する。
規約：射影と底の図式の充填性は要求しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、相対写像空間の宇宙調整の関手性。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：相対関手空間の宇宙移送は底上の射による後合成と可換。
方針：各内部 Hom の単体の出力への後合成を計算する。
規約：底上の可換性を宇宙持ち上げした等式で指定する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、復元比較の標的に関する宇宙移送の自然性。 -/
lemma uliftRelativeFunctorMap_post {A E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p) (a : A ⟶ B) :
    (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost p q f hf a) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftRelativeFunctorMap q a =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftRelativeFunctorMap p a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost
      ((SSet.uliftFunctor.{v, u}).map p) ((SSet.uliftFunctor.{v, u}).map q)
      ((SSet.uliftFunctor.{v, u}).map f) (by rw [← Functor.map_comp, hf])
      ((SSet.uliftFunctor.{v, u}).map a) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro g
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  rfl

/-- 概要：相対関手空間の宇宙移送は底の図式を制限する前合成と可換。
方針：内部 Hom の始域への前合成と ULift の往復を計算する。
規約：底の図式とその定義域を同時に持ち上げる。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、復元比較の始域に関する宇宙移送の自然性。 -/
lemma uliftRelativeFunctorMap_pre {D A E B : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (i : D ⟶ A) :
    (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p a i) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftRelativeFunctorMap p (i ≫ a) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftRelativeFunctorMap p a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre
      ((SSet.uliftFunctor.{v, u}).map p) ((SSet.uliftFunctor.{v, u}).map a)
      ((SSet.uliftFunctor.{v, u}).map i) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro g
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
