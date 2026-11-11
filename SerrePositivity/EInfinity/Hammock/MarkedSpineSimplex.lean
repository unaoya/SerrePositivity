module

public import SerrePositivity.EInfinity.Hammock.UnmarkedMarkedSpine

/-!
# 全因子が指定 hammock である有限切断列の全単体作用素

概要：終端と全 prefix を元の作用素で制限し、生成矢を保持する単体集合を構成する。
方針：有限切断列で再帰し、元の指定 hammock の恒等・合成則を使う。
規約：元の全因子と全生成文字列を保持する。
使われ方：元の hammock からの反復切断の単体的自然性。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open CategoryTheory

variable {C : Type u} [Category.{u} C] {W : MorphismProperty C} {Y : Paths C}
  {n m k : SimplexCategoryᵒᵖ}

def map (θ : n ⟶ m) {X : Paths C} : MarkedSpine W Y n X → MarkedSpine W Y m X
  | .nil X p => .nil X ((AllMarked.nativeSpace W X Y).map θ p)
  | .cons X g p t => .cons X g ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.left W X g.val).map θ p) (map θ t)

lemma map_id {X : Paths C} (t : MarkedSpine W Y n X) : map (𝟙 n) t = t := by
  induction t with
  | nil X p => exact congrArg (nil X) ((AllMarked.nativeSpace W X Y).map_id_apply n p)
  | cons X g p t ih =>
    change cons X g ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.left W X g.val).map (𝟙 n) p) (map (𝟙 n) t) = _
    rw [ih]
    exact congrArg (fun q => cons X g q t) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.left W X g.val).map_id_apply n p)

lemma map_comp (θ : n ⟶ m) (φ : m ⟶ k) {X : Paths C} (t : MarkedSpine W Y n X) :
    map (θ ≫ φ) t = map φ (map θ t) := by
  induction t with
  | nil X p => exact congrArg (nil X) ((AllMarked.nativeSpace W X Y).map_comp_apply θ φ p)
  | cons X g p t ih =>
    change cons X g ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.left W X g.val).map (θ ≫ φ) p) (map (θ ≫ φ) t) = _
    rw [ih]
    exact congrArg (fun q => cons X g q (map φ (map θ t)))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.left W X g.val).map_comp_apply θ φ p)

lemma word_map (θ : n ⟶ m) {X : Paths C} (t : MarkedSpine W Y n X) : (map θ t).word = t.word := by
  induction t with
  | nil => rfl
  | cons X g p t ih => exact congrArg (List.cons g.val) ih

variable (W Y)

def space (X : Paths C) : SSet.{u} where
  obj n := MarkedSpine W Y n X
  map θ := ↾fun t => map θ t
  map_id _ := by
    apply ConcreteCategory.hom_ext
    exact map_id
  map_comp θ φ := by
    apply ConcreteCategory.hom_ext
    exact map_comp θ φ

def wordValue (X : Paths C) : space W Y X ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj (List (Quiver.Total C)) where
  app _ := ↾fun t => t.word
  naturality _ _ θ := by
    apply ConcreteCategory.hom_ext
    exact word_map θ

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
