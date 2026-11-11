module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Hom

/-!
概要：h Fun 内の Kan の普遍写像性と、それが与える大域的一意性。
方針：指定自然変換による Hom の全単射から互いに逆な比較射を作る。
規約：ここでは Hom 全単射を明示的な仮定とする。点ごとの Kan 条件からの導出は別の工程。
使われ方：Kerodon Proposition 7.3.6.1（Tag 0309） の π₀ の帰結、Remark 7.3.6.6 の一意性の一般部分。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：右 Kan の指定自然変換による h Fun の Hom の比較。
方針：δ で前合成し、α を後合成する。
規約：入力は G → F、出力は Gδ → F₀。
使われ方：大域的な普遍写像性の正確な比較写像。 -/
def rightKanHomMap {K C D : SSet.{u}} (δ : K ⟶ C) {F₀ : K ⟶ D} {F : C ⟶ D}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (δ ≫ F) F₀) (G : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom G F → _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (δ ≫ G) F₀ :=
  fun η ↦ (hoFunctor.map ((pre δ).app D)).toFunctor.map η ≫ α

/-- 概要：左 Kan の指定自然変換による h Fun の Hom の比較。
方針：δ で前合成し、β を前に合成する。
規約：入力は F → G、出力は F₀ → Gδ。
使われ方：大域的な普遍写像性の正確な比較写像。 -/
def leftKanHomMap {K C D : SSet.{u}} (δ : K ⟶ C) {F₀ : K ⟶ D} {F : C ⟶ D}
    (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F₀ (δ ≫ F)) (G : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G → _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F₀ (δ ≫ G) :=
  fun η ↦ β ≫ (hoFunctor.map ((pre δ).app D)).toFunctor.map η

/-- 概要：指定自然変換が満たす右側の h Fun の普遍写像性。
方針：全ての G に対し上の正確な比較写像の全単射性を要求する。
規約：点ごとの Kan 拡張条件とは別の命題である。
使われ方：Kerodon Proposition 7.3.6.1（Tag 0309） の双対の π₀ の帰結。 -/
def RightKanHomUniversal {K C D : SSet.{u}} (δ : K ⟶ C) {F₀ : K ⟶ D} {F : C ⟶ D}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (δ ≫ F) F₀) : Prop :=
  ∀ G : C ⟶ D, Function.Bijective (rightKanHomMap δ α G)

/-- 概要：指定自然変換が満たす左側の h Fun の普遍写像性。
方針：全ての G に対し上の比較写像の全単射性を要求する。
規約：点ごとの Kan 拡張条件とは別の命題である。
使われ方：Kerodon Proposition 7.3.6.1（Tag 0309） の π₀ の帰結。 -/
def LeftKanHomUniversal {K C D : SSet.{u}} (δ : K ⟶ C) {F₀ : K ⟶ D} {F : C ⟶ D}
    (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F₀ (δ ≫ F)) : Prop :=
  ∀ G : C ⟶ D, Function.Bijective (leftKanHomMap δ β G)

/-- 概要：右側の普遍写像性を持つ二つの関手は h Fun 全体で同型。
方針：全射性で比較射を作り、単射性で両合成が恒等であることを示す。
規約：普遍写像性を明示的に仮定する。点ごとの値の同型は使わない。
使われ方：右 Kan 拡張の大域的一意性の一般部分。 -/
def rightKanHomUniversalIso {K C D : SSet.{u}} (δ : K ⟶ C) {F₀ : K ⟶ D} {F G : C ⟶ D}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (δ ≫ F) F₀) (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (δ ≫ G) F₀)
    (hF : RightKanHomUniversal δ α) (hG : RightKanHomUniversal δ β) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G := by
  let r := (hoFunctor.map ((pre δ).app D)).toFunctor
  let σ := Classical.choose ((hG F).2 α)
  let τ := Classical.choose ((hF G).2 β)
  have hσ : r.map σ ≫ β = α := Classical.choose_spec ((hG F).2 α)
  have hτ : r.map τ ≫ α = β := Classical.choose_spec ((hF G).2 β)
  refine ⟨σ, τ, ?_, ?_⟩
  · apply (hF F).1
    change r.map (σ ≫ τ) ≫ α = r.map (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F))) ≫ α
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.assoc, hτ, hσ]
  · apply (hG G).1
    change r.map (τ ≫ σ) ≫ β = r.map (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G))) ≫ β
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.assoc, hσ, hτ]

/-- 概要：右側の普遍写像性から得た同型は指定自然変換に両立する。
方針：比較射を選んだ全射性の仕様を使う。
規約：式は右 Kan の Hom 比較そのものを使う。
使われ方：単位・余単位を保つ大域的な比較。 -/
lemma rightKanHomUniversalIso_hom_fac {K C D : SSet.{u}} (δ : K ⟶ C)
    {F₀ : K ⟶ D} {F G : C ⟶ D}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (δ ≫ F) F₀) (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (δ ≫ G) F₀)
    (hF : RightKanHomUniversal δ α) (hG : RightKanHomUniversal δ β) :
    rightKanHomMap δ β F (rightKanHomUniversalIso δ α β hF hG).hom = α :=
  Classical.choose_spec ((hG F).2 α)

/-- 概要：左側の普遍写像性を持つ二つの関手は h Fun 全体で同型。
方針：全射性で比較射を作り、単射性で両合成を恒等にする。
規約：普遍写像性を明示的に仮定する。
使われ方：左 Kan 拡張の大域的一意性の一般部分。 -/
def leftKanHomUniversalIso {K C D : SSet.{u}} (δ : K ⟶ C) {F₀ : K ⟶ D} {F G : C ⟶ D}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F₀ (δ ≫ F)) (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F₀ (δ ≫ G))
    (hF : LeftKanHomUniversal δ α) (hG : LeftKanHomUniversal δ β) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G := by
  let r := (hoFunctor.map ((pre δ).app D)).toFunctor
  let σ := Classical.choose ((hF G).2 β)
  let τ := Classical.choose ((hG F).2 α)
  let α' : (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F₀) : hoFunctor.obj ((ihom K).obj D)) ⟶
      r.obj (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) := α
  let β' : (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F₀) : hoFunctor.obj ((ihom K).obj D)) ⟶
      r.obj (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) := β
  have hσ : α' ≫ r.map σ = β' := Classical.choose_spec ((hF G).2 β)
  have hτ : β' ≫ r.map τ = α' := Classical.choose_spec ((hG F).2 α)
  refine ⟨σ, τ, ?_, ?_⟩
  · apply (hF F).1
    change α' ≫ r.map (σ ≫ τ) = α' ≫ r.map (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)))
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      Category.comp_id, ← Category.assoc, hσ, hτ]
  · apply (hG G).1
    change β' ≫ r.map (τ ≫ σ) = β' ≫ r.map (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)))
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      Category.comp_id, ← Category.assoc, hτ, hσ]

/-- 概要：左側の普遍写像性から得た同型は指定自然変換に両立する。
方針：比較射の全射性の仕様を取り出す。
規約：式は左 Kan の Hom 比較そのものを使う。
使われ方：単位を保つ大域的な比較。 -/
lemma leftKanHomUniversalIso_hom_fac {K C D : SSet.{u}} (δ : K ⟶ C)
    {F₀ : K ⟶ D} {F G : C ⟶ D}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F₀ (δ ≫ F)) (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F₀ (δ ≫ G))
    (hF : LeftKanHomUniversal δ α) (hG : LeftKanHomUniversal δ β) :
    leftKanHomMap δ α G (leftKanHomUniversalIso δ α β hF hG).hom = β :=
  Classical.choose_spec ((hF G).2 β)

/-- 概要：右側の普遍比較同型の逆も指定自然変換に両立する。
方針：逆比較射を選んだ全射性の仕様を使う。
規約：逆射 G → F による Hom 比較。
使われ方：二方向の比較の正規化。 -/
lemma rightKanHomUniversalIso_inv_fac {K C D : SSet.{u}} (δ : K ⟶ C)
    {F₀ : K ⟶ D} {F G : C ⟶ D}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (δ ≫ F) F₀) (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (δ ≫ G) F₀)
    (hF : RightKanHomUniversal δ α) (hG : RightKanHomUniversal δ β) :
    rightKanHomMap δ α G (rightKanHomUniversalIso δ α β hF hG).inv = β :=
  Classical.choose_spec ((hF G).2 β)

/-- 概要：右側の普遍比較同型の射は指定自然変換との両立条件で一意。
方針：正確な Hom 比較の単射性を使う。
規約：h Fun 全体での等式。
使われ方：指定自然変換を保つ比較の一意性。 -/
lemma rightKanHomUniversalIso_hom_unique {K C D : SSet.{u}} (δ : K ⟶ C)
    {F₀ : K ⟶ D} {F G : C ⟶ D}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (δ ≫ F) F₀) (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (δ ≫ G) F₀)
    (hF : RightKanHomUniversal δ α) (hG : RightKanHomUniversal δ β)
    (σ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G) (hσ : rightKanHomMap δ β F σ = α) :
    σ = (rightKanHomUniversalIso δ α β hF hG).hom :=
  (hG F).1 (hσ.trans (rightKanHomUniversalIso_hom_fac δ α β hF hG).symm)

/-- 概要：左側の普遍比較同型の逆も指定自然変換に両立する。
方針：逆比較射の全射性の仕様を使う。
規約：逆射 G → F による Hom 比較。
使われ方：二方向の比較の正規化。 -/
lemma leftKanHomUniversalIso_inv_fac {K C D : SSet.{u}} (δ : K ⟶ C)
    {F₀ : K ⟶ D} {F G : C ⟶ D}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F₀ (δ ≫ F)) (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F₀ (δ ≫ G))
    (hF : LeftKanHomUniversal δ α) (hG : LeftKanHomUniversal δ β) :
    leftKanHomMap δ β F (leftKanHomUniversalIso δ α β hF hG).inv = α :=
  Classical.choose_spec ((hG F).2 α)

/-- 概要：左側の普遍比較同型の射は指定自然変換との両立条件で一意。
方針：Hom 比較の単射性を使う。
規約：h Fun 全体での等式。
使われ方：指定自然変換を保つ比較の一意性。 -/
lemma leftKanHomUniversalIso_hom_unique {K C D : SSet.{u}} (δ : K ⟶ C)
    {F₀ : K ⟶ D} {F G : C ⟶ D}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F₀ (δ ≫ F)) (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F₀ (δ ≫ G))
    (hF : LeftKanHomUniversal δ α) (hG : LeftKanHomUniversal δ β)
    (σ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G) (hσ : leftKanHomMap δ α G σ = β) :
    σ = (leftKanHomUniversalIso δ α β hF hG).hom :=
  (hF G).1 (hσ.trans (leftKanHomUniversalIso_hom_fac δ α β hF hG).symm)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
