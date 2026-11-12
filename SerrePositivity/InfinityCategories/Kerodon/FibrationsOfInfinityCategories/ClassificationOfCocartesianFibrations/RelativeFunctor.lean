module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorSpace
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorVertices

/-!
概要：相対関手空間の宇宙持ち上げと、持ち上げた底上の相対関手空間の同型。
方針：内部 Hom の宇宙移送を、指定された底の図式に一致する fiber の条件へ制限する。
規約：底への二つの射の充填性は不要。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、小さい相対写像空間と coherent な復元の比較の宇宙調整。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：相対関手空間の持ち上げを、持ち上げた底上の相対関手空間へ写す。
方針：内部 Hom の単体を持ち上げ、後合成と定値単体の計算で底の固定条件を移す。
規約：射影 p と図式 a は任意。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、相対写像空間の宇宙移送の順方向。 -/
def uliftRelativeFunctorMap {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) :
    (SSet.uliftFunctor.{v, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace ((SSet.uliftFunctor.{v, u}).map p) ((SSet.uliftFunctor.{v, u}).map a) where
  app n := ↾fun f => ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorHomUp f.down.val, by
    have h := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorHomUp.{u, v}) f.down.property
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorHomUp_post, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorHomUp_constant] at h
    exact h⟩
  naturality d e α := by
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    apply CategoryTheory.Functor.functorHom_ext
    intro k γ
    rfl

/-- 概要：持ち上げた底上の相対関手空間を、元の相対関手空間の持ち上げへ戻す。
方針：内部 Hom の単体を下ろし、持ち上げの単射性で底の固定条件を検出する。
規約：追加の宇宙 v は任意。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、相対写像空間の宇宙移送の逆方向。 -/
def uliftRelativeFunctorDown {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace ((SSet.uliftFunctor.{v, u}).map p) ((SSet.uliftFunctor.{v, u}).map a) ⟶
      (SSet.uliftFunctor.{v, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a) where
  app n := ↾fun f => ULift.up ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorHomDown f.val, by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorHomUp_injective.{u, v}
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorHomUp_post, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorHomUp_down, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorHomUp_constant]
    exact f.property⟩
  naturality d e α := by
    apply ConcreteCategory.hom_ext
    intro f
    apply ULift.ext
    apply Subtype.ext
    apply CategoryTheory.Functor.functorHom_ext
    intro k γ
    rfl

/-- 概要：相対関手空間の宇宙持ち上げは、持ち上げた射影と図式の相対関手空間と同型。
方針：内部 Hom の単体の持ち上げと下ろす操作の往復を fiber に制限する。
規約：単体集合の厳密な同型。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、元の小さい fibration の写像空間と復元の比較の接続。 -/
def uliftRelativeFunctorIso {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) :
    (SSet.uliftFunctor.{v, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace ((SSet.uliftFunctor.{v, u}).map p) ((SSet.uliftFunctor.{v, u}).map a) where
  hom := uliftRelativeFunctorMap p a
  inv := uliftRelativeFunctorDown p a
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro f
    apply ULift.ext
    apply Subtype.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorHomDown_up.{u, v} f.down.val
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorHomUp_down.{u, v} f.val

/-- 概要：相対関手空間の宇宙移送は、通常の底上の射の頂点を持ち上げた射の頂点へ写す。
方針：内部 Hom の単体の持ち上げを零単体で計算する。
規約：底上の射 f の可換性を持ち上げても厳密に保つ。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、相対写像空間の宇宙移送と通常の射の整合性。 -/
lemma uliftRelativeFunctorMap_vertex {A E B : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (f : A ⟶ E) (hf : f ≫ p = a) :
    (uliftRelativeFunctorMap.{u, v} p a).app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p a f hf)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex ((SSet.uliftFunctor.{v, u}).map p) ((SSet.uliftFunctor.{v, u}).map a)
        ((SSet.uliftFunctor.{v, u}).map f) (by rw [← Functor.map_comp, hf]) := by
  apply Subtype.ext
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
