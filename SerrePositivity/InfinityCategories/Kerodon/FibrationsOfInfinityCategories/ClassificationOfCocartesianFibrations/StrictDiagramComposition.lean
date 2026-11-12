module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictTransportMappingEquivalence

/-!
概要：strict な自然変換の空間の単位と豊穣合成。
方針：内部 Hom の単体の共通パラメーターにおける合成を対象ごとに行う。
規約：係数図式の Kan 性はこの構成に不要。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strict transport の像を coherent nerve に移すための単体的圏。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：strict な変換空間の豊穣単位。
方針：各対象でパラメーターを無視した恒等写像を選ぶ。
規約：始域は単体集合のテンソル単位。
使われ方：Kerodon §5.3.1（Tag 035D）、strict な図式の豊穣恒等射。 -/
def strictDiagramMappingIdentity {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) :
    𝟙_ SSet.{u} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F F where
  app _ := ↾fun _ ↦ ⟨fun c ↦ Functor.HomObj.ofNatTrans (𝟙 (F.obj c)), by
    intro c d f k α x
    rfl⟩
  naturality _ _ _ := rfl

/-- 概要：同じ底上の二つの strict な自然変換を豊穣的に合成する。
方針：各対象で内部 Hom の単体を共通のパラメーターにおいて合成する。
規約：合成の順は F から G、次に G から H。
使われ方：Kerodon §5.3.1（Tag 035D）、strict transport の像の高次の射の合成。 -/
def strictDiagramMappingComposition {C : Type u} [Category.{u} C]
    (F G H : C ⥤ SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F G ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace G H ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F H where
  app _ := ↾fun ⟨η, θ⟩ ↦ ⟨fun c ↦ Functor.HomObj.comp (η.val c) (θ.val c), by
    intro c d f k α x
    change (H.map f).app k ((θ.val c).app k α ((η.val c).app k α x)) =
      (θ.val d).app k α ((η.val d).app k α ((F.map f).app k x))
    rw [θ.property f k α, η.property f k α]⟩
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨η, θ⟩
    apply Subtype.ext
    funext c
    apply CategoryTheory.Functor.functorHom_ext
    intro k β
    apply ConcreteCategory.hom_ext
    intro x
    rfl

/-- 概要：strict な変換の豊穣合成は左の恒等変換を消去する。
方針：各対象と各パラメーターの入力で恒等写像の合成を計算する。
規約：恒等変換は F の側に置く。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strict な図式の豊穣圏の左単位則。 -/
lemma strictDiagramMappingIdentity_comp {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) :
    (λ_ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F G)).inv ≫ strictDiagramMappingIdentity F ▷ _ ≫
      strictDiagramMappingComposition F F G = 𝟙 _ := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro η
  apply Subtype.ext
  funext c
  apply CategoryTheory.Functor.functorHom_ext
  intro k α
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 概要：strict な変換の豊穣合成は右の恒等変換を消去する。
方針：各対象と各パラメーターの入力で恒等写像の合成を計算する。
規約：恒等変換は G の側に置く。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strict な図式の豊穣圏の右単位則。 -/
lemma strictDiagramMappingComposition_id {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) :
    (ρ_ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F G)).inv ≫ _ ◁ strictDiagramMappingIdentity G ≫
      strictDiagramMappingComposition F G G = 𝟙 _ := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro η
  apply Subtype.ext
  funext c
  apply CategoryTheory.Functor.functorHom_ext
  intro k α
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 概要：strict な変換の豊穣合成は結合的。
方針：共通のパラメーターで三つの写像を対象ごとに順に評価する。
規約：結合子でテンソル因子の括弧を揃える。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strict な図式の単体的圏の結合則。 -/
lemma strictDiagramMappingComposition_assoc {C : Type u} [Category.{u} C]
    (F G H I : C ⥤ SSet.{u}) :
    (α_ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F G) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace G H)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace H I)).inv ≫ strictDiagramMappingComposition F G H ▷ _ ≫
        strictDiagramMappingComposition F H I =
      _ ◁ strictDiagramMappingComposition G H I ≫ strictDiagramMappingComposition F G I := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨η, θ, κ⟩
  apply Subtype.ext
  funext c
  apply CategoryTheory.Functor.functorHom_ext
  intro k α
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 概要：strict な変換空間への射は全対象での成分が同じなら等しい。
方針：各次数の部分型と成分の関数の外延性を使う。
規約：パラメーターの始域 A は任意。
使われ方：Kerodon §5.3.1（Tag 035D）、strict な図式への豊穣関手の法則を成分ごとに検証する。 -/
lemma strictDiagramMappingHom_ext {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} {A : SSet.{u}} {f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F G}
    (h : ∀ c, f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent F G c =
      g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent F G c) : f = g := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  funext c
  exact congrArg (fun k : A ⟶ (ihom (F.obj c)).obj (G.obj c) ↦ k.app n x) (h c)

/-- 概要：strict な図式の豊穣単位の各成分は内部 Hom の豊穣単位。
方針：各単体の恒等の族を計算する。
規約：底の対象 c を固定する。
使われ方：Kerodon §5.3.1（Tag 035D）、対象ごとの豊穣評価の単位則。 -/
lemma strictDiagramMappingIdentity_component {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) :
    strictDiagramMappingIdentity F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent F F c =
      MonoidalClosed.id (F.obj c) := rfl

/-- 概要：strict な変換の豊穣合成を一対象で評価すると内部 Hom の豊穣合成になる。
方針：uncurry した二つの射を各単体の入力で比較する。
規約：二つの成分は同じ底の対象 c で取る。
使われ方：Kerodon §5.3.1（Tag 035D）、対象ごとの豊穣評価の合成則。 -/
lemma strictDiagramMappingComposition_component {C : Type u} [Category.{u} C]
    (F G H : C ⥤ SSet.{u}) (c : C) :
    strictDiagramMappingComposition F G H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent F H c =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent F G c ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent G H c) ≫
        MonoidalClosed.comp (F.obj c) (G.obj c) (H.obj c) := by
  apply uncurry_injective
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, η, θ⟩
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
