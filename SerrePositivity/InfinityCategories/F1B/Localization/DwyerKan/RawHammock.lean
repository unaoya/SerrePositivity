module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ColimitGraph
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.IdentityColumn

/-!
# 元の全固定語の未縮約 hammock

概要：各次数の元の全語の全射列を、語も保持する依存和として束ねる。
方針：元の全作用素と元の余極限への標準射をそのまま使う。
規約：長さや同方向の列をまだ同一視しない。
使われ方：基本縮約・停止性・縮約 hammock との実同型。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (X Y : C)

/-- 元の語とその次数の全射列を保つ未縮約 hammock。 -/
def RawHammock (n : SimplexCategoryᵒᵖ) := Σ w : Word, (graph W w X Y).obj n

namespace RawHammock
variable {n m : SimplexCategoryᵒᵖ}

def map (α : n ⟶ m) (r : RawHammock W X Y n) : RawHammock W X Y m :=
  ⟨r.1, (graph W r.1 X Y).map α r.2⟩

/-- 同じ元の語の標準射による余極限内の値。 -/
def value (r : RawHammock W X Y n) : (colimitGraph W X Y).obj n :=
  (graphInclusion W X Y r.1).app n r.2

lemma value_map (α : n ⟶ m) (r : RawHammock W X Y n) :
    value W X Y (map W X Y α r) = (colimitGraph W X Y).map α (value W X Y r) :=
  NatTrans.naturality_apply (graphInclusion W X Y r.1) α r.2

/-- 元の全語の遷移は、同じ元の余極限内の値を保持する。 -/
lemma value_transition {a b : Word} (f : a ⟶ b) (τ : (graph W a X Y).obj n) :
    value W X Y ⟨b, ((graphDiagram W X Y).map f).app n τ⟩ = value W X Y ⟨a, τ⟩ := by
  exact congrArg (fun η : graph W a X Y ⟶ colimitGraph W X Y => η.app n τ)
    (graphInclusion_naturality W X Y f)

/-- 原典の縮約条件：列の方向は交互で、全行が恒等である列はない。 -/
def IsReduced (r : RawHammock W X Y n) : Prop :=
  (∀ i j : Fin r.1.length, j.val = i.val + 1 → r.1.direction i ≠ r.1.direction j) ∧
    ∀ j : Fin r.1.length, ¬ ∀ k, IdentityColumn (r.2.obj k) j

end RawHammock
end SerrePositivity.EInfinity.Hammock
