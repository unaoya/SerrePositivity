module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitGraph
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityColumn

/-!
# 元の全固定語の未縮約 hammock

概要：各次数の元の全語の全射列を、語も保持する依存和として束ねる。
方針：元の全作用素と元の余極限への標準射をそのまま使う。
規約：長さや同方向の列をまだ同一視しない。
使われ方：基本縮約・停止性・縮約 hammock との実同型。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (X Y : C)

/-- 元の語とその次数の全射列を保つ未縮約 hammock。 -/
def RawHammock (n : SimplexCategoryᵒᵖ) := Σ w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word, (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W w X Y).obj n

namespace RawHammock
variable {n m : SimplexCategoryᵒᵖ}

def map (α : n ⟶ m) (r : RawHammock W X Y n) : RawHammock W X Y m :=
  ⟨r.1, (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W r.1 X Y).map α r.2⟩

/-- 同じ元の語の標準射による余極限内の値。 -/
def value (r : RawHammock W X Y n) : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y).obj n :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y r.1).app n r.2

lemma value_map (α : n ⟶ m) (r : RawHammock W X Y n) :
    value W X Y (map W X Y α r) = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y).map α (value W X Y r) :=
  NatTrans.naturality_apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y r.1) α r.2

/-- 元の全語の遷移は、同じ元の余極限内の値を保持する。 -/
lemma value_transition {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W a X Y).obj n) :
    value W X Y ⟨b, ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map f).app n τ⟩ = value W X Y ⟨a, τ⟩ := by
  exact congrArg (fun η : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W a X Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y => η.app n τ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion_naturality W X Y f)

/-- 原典の縮約条件：列の方向は交互で、全行が恒等である列はない。 -/
def IsReduced (r : RawHammock W X Y n) : Prop :=
  (∀ i j : Fin r.1.length, j.val = i.val + 1 → r.1.direction i ≠ r.1.direction j) ∧
    ∀ j : Fin r.1.length, ¬ ∀ k, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityColumn (r.2.obj k) j

end RawHammock
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
