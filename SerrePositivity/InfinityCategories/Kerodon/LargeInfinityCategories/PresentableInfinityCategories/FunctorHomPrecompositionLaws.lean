module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LeftClassificationBaseChangeHom
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.StraighteningBaseChangeRestriction

/-!
概要：指定関手間射の前合成の関手性と、充満忠実な内部前合成による等式の反映。
方針：既存の正規化した射作用を同じホモトピー圏の射作用へ戻す。
規約：元の指定射を保持する。
使われ方：Kerodon §5.6（Tag 027M）の指定分類底変換の合成則の降下。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories
namespace PresentableInfinityCategories

/-- 概要：指定射の前合成は同じ内部前合成の射作用。
方針：定義の恒等端点移送を消す。規約：元の射。使われ方：前合成の計算法則。 -/
lemma precomposeFunctorHom_eq_map {A B X : SSet.{u}}
    (k : B ⟶ A) {f g : A ⟶ X} (α : FunctorHom f g) :
    precomposeFunctorHom k α =
      (hoFunctor.map ((pre k).app X)).toFunctor.map α := by
  simp only [precomposeFunctorHom, normalizedVertexHomMap, eqToHom_refl,
    Category.id_comp, Category.comp_id]

/-- 概要：指定射の前合成は合成を保つ。
方針：同じ内部前合成の関手性を使う。規約：元の射。使われ方：貼り合わせ式の制限。 -/
lemma precomposeFunctorHom_comp {A B X : SSet.{u}} (k : B ⟶ A)
    {f g h : A ⟶ X} (α : FunctorHom f g) (β : FunctorHom g h) :
    precomposeFunctorHom k (α ≫ β) =
      precomposeFunctorHom k α ≫ precomposeFunctorHom k β := by
  simp only [precomposeFunctorHom_eq_map, Functor.map_comp]

/-- 概要：充満忠実な内部前合成は指定射の等式を反映する。
方針：同じホモトピー圏の関手の忠実性を使う。
規約：元の二射を比較する。使われ方：初頂点制限から同じ底変換式を降下する。 -/
lemma precomposeFunctorHom_injective {A B X : SSet.{u}} [Quasicategory X]
    (k : B ⟶ A)
    (hk : Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful
      ((pre k).app X))
    {f g : A ⟶ X} (α β : FunctorHom f g)
    (h : precomposeFunctorHom k α = precomposeFunctorHom k β) : α = β := by
  apply hk.toHoFullyFaithful.map_injective
  simpa only [precomposeFunctorHom_eq_map] using h

end PresentableInfinityCategories
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories
