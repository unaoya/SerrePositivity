module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorVertices

/-!
概要：底上の相対関手空間どうしの豊穣合成。
方針：二つの評価を共通のパラメーターで合成し、底を保つ族として curry する。
規約：射影の充填性は不要で、全ての底上の対象を扱う。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、left fibrations の単体的圏の Hom の合成。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：相対関手空間の全てのパラメーターを評価する射。
方針：恒等射を相対 uncurry する。
規約：定義域の第一成分が元の図式、第二成分が相対関手。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、二つの相対関手の合成の評価。 -/
def relativeFunctorEvaluation {B : SSet.{u}} (a b : Over B) :
    a.left ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace b.hom a.hom ⟶ b.left :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace b.hom a.hom))

/-- 概要：相対関手の評価は指定された底上の図式を被覆する。
方針：相対 uncurry の射影の式を用いる。
規約：相対関手のパラメーター依存を第一射影で忘れる。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、合成した評価が底を保つことの確認。 -/
lemma relativeFunctorEvaluation_projection {B : SSet.{u}} (a b : Over B) :
    relativeFunctorEvaluation a b ≫ b.hom =
      fst a.left (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace b.hom a.hom) ≫ a.hom :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_projection _

/-- 概要：底上の相対関手空間の二つの射を豊穣的に合成する。
方針：結合子の逆で二つのパラメーターを順に評価し、得た底上の族を相対 curry する。
規約：合成の順は a から b、次に b から c。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、left fibration の関手空間を Hom とする単体的圏。 -/
def relativeFunctorComposition {B : SSet.{u}} (a b c : Over B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace b.hom a.hom ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace c.hom b.hom ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace c.hom a.hom :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorCurry
    ((α_ a.left (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace b.hom a.hom) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace c.hom b.hom)).inv ≫
      relativeFunctorEvaluation a b ▷ _ ≫ relativeFunctorEvaluation b c) (by
    rw [Category.assoc, Category.assoc, relativeFunctorEvaluation_projection,
      ← Category.assoc (relativeFunctorEvaluation a b ▷ _), whiskerRight_fst,
      Category.assoc, relativeFunctorEvaluation_projection]
    simp only [associator_inv_fst_fst_assoc])

/-- 概要：相対合成を内部 Hom に含めると通常の内部 Hom の合成になる。
方針：両辺を uncurry し、各次数の二つの評価を比較する。
規約：二つの fiber の包含をテンソルしてから閉構造の合成を適用する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、単位則と結合則を通常の内部 Hom から移す。 -/
lemma relativeFunctorComposition_ι {B : SSet.{u}} (a b c : Over B) :
    relativeFunctorComposition a b c ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom a.left).map c.hom) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a.hom) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom a.left).map b.hom) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a.hom) ⊗ₘ
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom b.left).map c.hom) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex b.hom)) ≫
      MonoidalClosed.comp a.left b.left c.left := by
  apply uncurry_injective
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, f, g⟩
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
