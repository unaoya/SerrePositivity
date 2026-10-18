module

public import SerrePositivity.InfinityCategories.F1.RelativeFunctorComposition

/-!
概要：相対関手空間の豊穣単位と合成の単位則・結合則。
方針：単位を恒等関手の族とし、各次数の相対関手の値で合成を比較する。
規約：全ての等式は単体集合の射の厳密な等式。
使われ方：Kerodon Corollary 5.6.0.6、left fibrations の単体的圏の構造法則。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：底上の対象の相対関手空間の豊穣単位。
方針：右単位子を恒等関手の族として相対 curry する。
規約：単位の始域は単体集合のテンソル単位。
使われ方：Kerodon Corollary 5.6.0.6、left fibration の豊穣恒等射。 -/
def relativeFunctorIdentity {B : SSet.{u}} (a : Over B) :
    𝟙_ SSet.{u} ⟶ relativeFunctorSpace a.hom a.hom :=
  relativeFunctorCurry (ρ_ a.left).hom (by rfl)

/-- 概要：相対豊穣単位は内部 Hom の豊穣単位を持ち上げた射。
方針：fiber の包含の後で curry された右単位子を計算する。
規約：内部 Hom 側は閉構造の恒等射。
使われ方：Kerodon Corollary 5.6.0.6、通常の単位則との整合性。 -/
lemma relativeFunctorIdentity_ι {B : SSet.{u}} (a : Over B) :
    relativeFunctorIdentity a ≫
      vertexFiberι ((ihom a.left).map a.hom) (functorVertex a.hom) =
      MonoidalClosed.id a.left := rfl

/-- 概要：相対合成は左の豊穣単位を消去する。
方針：各次数の関手を各入力で評価し、恒等写像との合成を計算する。
規約：合成の先頭に a の恒等関手を置く。
使われ方：Kerodon Corollary 5.6.0.6、相対関手空間の左単位則。 -/
lemma relativeFunctorIdentity_comp {B : SSet.{u}} (a b : Over B) :
    (λ_ (relativeFunctorSpace b.hom a.hom)).inv ≫
      relativeFunctorIdentity a ▷ _ ≫ relativeFunctorComposition a a b = 𝟙 _ := by
  apply vertexFiber_hom_ext
  rw [Category.id_comp, Category.assoc, Category.assoc, relativeFunctorComposition_ι,
    tensorHom_def]
  dsimp only [relativeFunctorSpace]
  simp only [Category.assoc]
  rw [← comp_whiskerRight_assoc, relativeFunctorIdentity_ι]
  rw [← whisker_exchange_assoc, ← leftUnitor_inv_naturality_assoc,
    MonoidalClosed.id_comp, Category.comp_id]

/-- 概要：相対合成は右の豊穣単位を消去する。
方針：各次数の関手を各入力で評価し、恒等写像との合成を計算する。
規約：合成の末尾に b の恒等関手を置く。
使われ方：Kerodon Corollary 5.6.0.6、相対関手空間の右単位則。 -/
lemma relativeFunctorComposition_id {B : SSet.{u}} (a b : Over B) :
    (ρ_ (relativeFunctorSpace b.hom a.hom)).inv ≫
      _ ◁ relativeFunctorIdentity b ≫ relativeFunctorComposition a b b = 𝟙 _ := by
  apply vertexFiber_hom_ext
  rw [Category.id_comp, Category.assoc, Category.assoc, relativeFunctorComposition_ι,
    tensorHom_def']
  dsimp only [relativeFunctorSpace]
  simp only [Category.assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, relativeFunctorIdentity_ι]
  rw [whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc,
    MonoidalClosed.comp_id, Category.comp_id]

/-- 概要：相対関手空間の豊穣合成は結合的。
方針：三つの関手を共通のパラメーターで評価し、同じ合成として比較する。
規約：結合子の逆により二つの括弧付けを揃える。
使われ方：Kerodon Corollary 5.6.0.6、left fibrations の単体的圏の結合則。 -/
lemma relativeFunctorComposition_assoc {B : SSet.{u}} (a b c d : Over B) :
    (α_ (relativeFunctorSpace b.hom a.hom) (relativeFunctorSpace c.hom b.hom)
      (relativeFunctorSpace d.hom c.hom)).inv ≫
      relativeFunctorComposition a b c ▷ _ ≫ relativeFunctorComposition a c d =
    _ ◁ relativeFunctorComposition b c d ≫ relativeFunctorComposition a b d := by
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

end SerrePositivity.InfinityCategories
