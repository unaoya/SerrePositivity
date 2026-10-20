module

public import SerrePositivity.InfinityCategories.F1.CocartesianRelativeFunctor

/-!
概要：cocartesian 関手の相対 Hom に元の豊穣単位・合成を制限する。
方針：頂点での辺の保存条件で持ち上げ、全部分複体の包含後に元の単位・結合則を使う。
規約：全パラメーターの実際の相対合成を保つ。Kan 性はまだ主張しない。
使われ方：cocartesian fibrations の単体的圏の core 移送前の豊穣構造。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- cocartesian 関手の相対空間から、元の全相対関手空間への包含。 -/
def cocartesianRelativeFunctorInclusion {E F B : SSet.{u}} (p : E ⟶ B) (q : F ⟶ B) :
    cocartesianRelativeFunctorSpace p q ⟶ relativeFunctorSpace q p :=
  (fullSubcomplexOnVertices _ (cocartesianRelativeFunctorPredicate p q)).ι

/-- 元の相対豊穣単位を、cocartesian 関手の全部分複体へ持ち上げる。 -/
def cocartesianRelativeFunctorIdentity {B : SSet.{u}} (a : Over B) :
    𝟙_ SSet.{u} ⟶ cocartesianRelativeFunctorSpace a.hom a.hom :=
  fullSubcomplexLift _ (relativeFunctorIdentity a) (by
    rintro ⟨⟩
    have h : (relativeFunctorIdentity a).app (Opposite.op ⦋0⦌) PUnit.unit =
        relativeFunctorVertex a.hom a.hom (𝟙 a.left) (Category.id_comp _) := by
      apply Subtype.ext
      rfl
    rw [h, cocartesianRelativeFunctorPredicate_vertex]
    exact preservesCocartesianEdges_id _)

/-- 元の相対豊穣合成を、cocartesian 関手の全部分複体へ持ち上げる。 -/
def cocartesianRelativeFunctorComposition {B : SSet.{u}} (a b c : Over B) :
    cocartesianRelativeFunctorSpace a.hom b.hom ⊗
      cocartesianRelativeFunctorSpace b.hom c.hom ⟶
      cocartesianRelativeFunctorSpace a.hom c.hom :=
  fullSubcomplexLift _
    ((cocartesianRelativeFunctorInclusion a.hom b.hom ⊗ₘ
      cocartesianRelativeFunctorInclusion b.hom c.hom) ≫ relativeFunctorComposition a b c) (by
      intro s
      exact cocartesianRelativeFunctorPredicate_comp a b c s.1.val s.2.val
        (fullSubcomplexOnVertices_vertex s.1) (fullSubcomplexOnVertices_vertex s.2))

/-- 制限した豊穣単位は、包含後に元の相対豊穣単位そのものとなる。 -/
lemma cocartesianRelativeFunctorIdentity_ι {B : SSet.{u}} (a : Over B) :
    cocartesianRelativeFunctorIdentity a ≫ cocartesianRelativeFunctorInclusion a.hom a.hom =
      relativeFunctorIdentity a := rfl

/-- 制限した豊穣合成は、包含後に元の相対豊穣合成そのものとなる。 -/
lemma cocartesianRelativeFunctorComposition_ι {B : SSet.{u}} (a b c : Over B) :
    cocartesianRelativeFunctorComposition a b c ≫ cocartesianRelativeFunctorInclusion a.hom c.hom =
      (cocartesianRelativeFunctorInclusion a.hom b.hom ⊗ₘ
        cocartesianRelativeFunctorInclusion b.hom c.hom) ≫ relativeFunctorComposition a b c := rfl

/-- 元の左単位則は、cocartesian 関手の全部分複体に厳密に制限される。 -/
lemma cocartesianRelativeFunctorIdentity_comp {B : SSet.{u}} (a b : Over B) :
    (λ_ (cocartesianRelativeFunctorSpace a.hom b.hom)).inv ≫
      cocartesianRelativeFunctorIdentity a ▷ _ ≫ cocartesianRelativeFunctorComposition a a b =
      𝟙 _ := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro f
  apply Subtype.ext
  exact congrArg (fun k ↦ k.app n f.val) (relativeFunctorIdentity_comp a b)

/-- 元の右単位則は、cocartesian 関手の全部分複体に厳密に制限される。 -/
lemma cocartesianRelativeFunctorComposition_id {B : SSet.{u}} (a b : Over B) :
    (ρ_ (cocartesianRelativeFunctorSpace a.hom b.hom)).inv ≫
      _ ◁ cocartesianRelativeFunctorIdentity b ≫ cocartesianRelativeFunctorComposition a b b =
      𝟙 _ := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro f
  apply Subtype.ext
  exact congrArg (fun k ↦ k.app n f.val) (relativeFunctorComposition_id a b)

/-- 元の結合則は、cocartesian 関手の全部分複体に厳密に制限される。 -/
lemma cocartesianRelativeFunctorComposition_assoc {B : SSet.{u}} (a b c d : Over B) :
    (α_ (cocartesianRelativeFunctorSpace a.hom b.hom)
      (cocartesianRelativeFunctorSpace b.hom c.hom)
      (cocartesianRelativeFunctorSpace c.hom d.hom)).inv ≫
      cocartesianRelativeFunctorComposition a b c ▷ _ ≫
        cocartesianRelativeFunctorComposition a c d =
    _ ◁ cocartesianRelativeFunctorComposition b c d ≫
      cocartesianRelativeFunctorComposition a b d := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨f, g, h⟩
  apply Subtype.ext
  exact congrArg (fun k ↦ k.app n (f.val, g.val, h.val))
    (relativeFunctorComposition_assoc a b c d)

end SerrePositivity.InfinityCategories
