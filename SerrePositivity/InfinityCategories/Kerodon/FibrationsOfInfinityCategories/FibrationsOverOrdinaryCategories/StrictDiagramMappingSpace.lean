module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorEnrichedEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.LeftStrictTransportWeightedNerve

/-!
概要：通常の圏上の単体集合値図式の strict な自然変換の空間。
方針：対象ごとの内部 Hom の単体の族に、底の各射についての厳密な自然性を課す。
規約：これは通常の単体集合の構成であり、𝒮 の極限の存在は主張しない。
使われ方：Kerodon Construction 5.3.1.5（Tag 035J）、Corollary 5.6.0.6（Tag 028T）、strict transport の写像空間の比較。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：strict な自然変換の指定次数の単体。
方針：内部 Hom の単体の対象ごとの族と、前合成・後合成による自然性を部分型にまとめる。
規約：F と G の Kan 性は要求しない。
使われ方：Kerodon §5.3.1（Tag 035D）、図式の全次数の自然変換を直接扱う。 -/
def strictDiagramMappingSimplex {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) (n : SimplexCategoryᵒᵖ) : Type u :=
  {η : ∀ c, ((ihom (F.obj c)).obj (G.obj c)).obj n //
    ∀ {c d : C} (f : c ⟶ d) (k : SimplexCategoryᵒᵖ) (α : n ⟶ k) (x : (F.obj c).obj k),
      (G.map f).app k ((η c).app k α x) = (η d).app k α ((F.map f).app k x)}

/-- 概要：strict な自然変換の単体を単体圏の射で制限する。
方針：各対象の内部 Hom の単体を制限し、前合成・後合成の自然性で条件を保つ。
規約：全対象で同じ面または退化を適用する。
使われ方：Kerodon §5.3.1（Tag 035D）、strict な自然変換の単体集合の構造。 -/
def strictDiagramMappingSimplexMap {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m)
    (η : strictDiagramMappingSimplex F G n) : strictDiagramMappingSimplex F G m := by
  refine ⟨(fun c : C ↦ ((ihom (F.obj c)).obj (G.obj c)).map α (η.val c)), ?_⟩
  intro c d f k β x
  exact η.property f k (α ≫ β) x

/-- 概要：通常の圏上の単体集合値図式の strict な自然変換の単体集合。
方針：対象ごとの内部 Hom の族に自然性を課し、面と退化を成分ごとに定める。
規約：一般の F と G に Kan 性を主張しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strict transport 間の高次の自然変換の比較先。 -/
def strictDiagramMappingSpace {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) : SSet.{u} where
  obj := strictDiagramMappingSimplex F G
  map α := ↾strictDiagramMappingSimplexMap F G α
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro η
    apply Subtype.ext
    funext c
    exact Functor.map_id_apply ((ihom (F.obj c)).obj (G.obj c)) n (η.val c)
  map_comp α β := by
    apply ConcreteCategory.hom_ext
    intro η
    apply Subtype.ext
    funext c
    exact Functor.map_comp_apply ((ihom (F.obj c)).obj (G.obj c)) α β (η.val c)

/-- 概要：strict な自然変換の空間から一対象での内部 Hom への評価。
方針：自然変換の各単体の指定した成分を取り出す。
規約：底の対象 c は固定する。
使われ方：Kerodon §5.3.1（Tag 035D）、自然変換の族を対象ごとに評価する。 -/
def strictDiagramMappingComponent {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) (c : C) :
    strictDiagramMappingSpace F G ⟶ (ihom (F.obj c)).obj (G.obj c) where
  app _ := ↾fun η ↦ η.val c
  naturality _ _ _ := rfl

/-- 概要：strict transport は相対 Hom の全空間から strict な自然変換の空間への射を誘導する。
方針：各 undercategory 上の相対 Hom に後合成し、前合成と後合成の可換性を計算する。
規約：p と q の left fibration 性はこの射の構成には不要。
使われ方：Kerodon Construction 5.3.1.5（Tag 035J）、Corollary 5.6.0.6（Tag 028T）、straightening の写像空間上の作用。 -/
def leftStrictTransportMappingSpaceMap {C : Type u} [Category.{u} C] {E E' : SSet.{u}}
    (p : E ⟶ nerve C) (q : E' ⟶ nerve C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q p ⟶
      strictDiagramMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q) where
  app n := ↾fun x ↦ ⟨fun c ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorPostHom
    (Over.mk (nerveMap (Under.forget c))) (Over.mk p) (Over.mk q)).app n x, by
      intro c d f k α y
      apply Subtype.ext
      rfl⟩
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    funext c
    apply CategoryTheory.Functor.functorHom_ext
    intro d β
    apply ConcreteCategory.hom_ext
    intro y
    apply Subtype.ext
    apply CategoryTheory.Functor.functorHom_ext
    intro k γ
    apply ConcreteCategory.hom_ext
    intro z
    rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
