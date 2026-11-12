module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorComposition

/-!
概要：相対関手空間の豊穣単位と合成の単位則・結合則。
方針：単位を恒等関手の族とし、各次数の相対関手の値で合成を比較する。
規約：全ての等式は単体集合の射の厳密な等式。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、left fibrations の単体的圏の構造法則。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：底上の対象の相対関手空間の豊穣単位。
方針：右単位子を恒等関手の族として相対 curry する。
規約：単位の始域は単体集合のテンソル単位。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、left fibration の豊穣恒等射。 -/
def relativeFunctorIdentity {B : SSet.{u}} (a : Over B) :
    𝟙_ SSet.{u} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace a.hom a.hom :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorCurry (ρ_ a.left).hom (by rfl)

/-- 概要：相対豊穣単位は内部 Hom の豊穣単位を持ち上げた射。
方針：fiber の包含の後で curry された右単位子を計算する。
規約：内部 Hom 側は閉構造の恒等射。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、通常の単位則との整合性。 -/
lemma relativeFunctorIdentity_ι {B : SSet.{u}} (a : Over B) :
    relativeFunctorIdentity a ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom a.left).map a.hom) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a.hom) =
      MonoidalClosed.id a.left := rfl

/-- 概要：相対合成は左の豊穣単位を消去する。
方針：各次数の関手を各入力で評価し、恒等写像との合成を計算する。
規約：合成の先頭に a の恒等関手を置く。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、相対関手空間の左単位則。 -/
lemma relativeFunctorIdentity_comp {B : SSet.{u}} (a b : Over B) :
    (λ_ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace b.hom a.hom)).inv ≫
      relativeFunctorIdentity a ▷ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition a a b = 𝟙 _ := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext
  rw [Category.id_comp, Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition_ι,
    tensorHom_def]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace]
  simp only [Category.assoc]
  rw [← comp_whiskerRight_assoc, relativeFunctorIdentity_ι]
  rw [← whisker_exchange_assoc, ← leftUnitor_inv_naturality_assoc,
    MonoidalClosed.id_comp, Category.comp_id]

/-- 概要：相対合成は右の豊穣単位を消去する。
方針：各次数の関手を各入力で評価し、恒等写像との合成を計算する。
規約：合成の末尾に b の恒等関手を置く。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、相対関手空間の右単位則。 -/
lemma relativeFunctorComposition_id {B : SSet.{u}} (a b : Over B) :
    (ρ_ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace b.hom a.hom)).inv ≫
      _ ◁ relativeFunctorIdentity b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition a b b = 𝟙 _ := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext
  rw [Category.id_comp, Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition_ι,
    tensorHom_def']
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace]
  simp only [Category.assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, relativeFunctorIdentity_ι]
  rw [whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc,
    MonoidalClosed.comp_id, Category.comp_id]

/-- 概要：相対関手空間の豊穣合成は結合的。
方針：三つの関手を共通のパラメーターで評価し、同じ合成として比較する。
規約：結合子の逆により二つの括弧付けを揃える。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、left fibrations の単体的圏の結合則。 -/
lemma relativeFunctorComposition_assoc {B : SSet.{u}} (a b c d : Over B) :
    (α_ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace b.hom a.hom) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace c.hom b.hom)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace d.hom c.hom)).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition a b c ▷ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition a c d =
    _ ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition b c d ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition a b d := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨f, g, h⟩
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro e α
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
