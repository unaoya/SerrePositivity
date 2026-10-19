module
public import SerrePositivity.KST.SConstruction.MappedPathTriangles

/-! # 因子三角形と交差正方形の指定辺の貼り合わせ
概要：端点の表示が異なる図式でも、共有する一単体を保って外側の三角形を得る。
方針：因子三角形の外側の辺で内部の辺を付け直し、交差正方形の二つの三角形を貼る。
規約：与えられた全ての外側の辺と共有する一単体を変更しない。
使われ方：自然性の因子分解三角形・因子の合成三角形・交差族を同時に接続する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 各共有辺の一単体の等号だけで、因子分解・左右の合成・交差正方形を貼り合わせる。 -/
lemma nonemptyCompStruct_paste_factorization_diagram {K : SSet.{u}} [Quasicategory K]
    {x₀ x₁ x₂ m₀₁ m₁₂ m₀₂ : K _⦋0⦌}
    (a₀₁ : K.Edge x₀ m₀₁) (b₀₁ : K.Edge m₀₁ x₁) (e₀₁ : K.Edge x₀ x₁)
    (a₁₂ : K.Edge x₁ m₁₂) (b₁₂ : K.Edge m₁₂ x₂) (e₁₂ : K.Edge x₁ x₂)
    (a₀₂ : K.Edge x₀ m₀₂) (b₀₂ : K.Edge m₀₂ x₂) (e₀₂ : K.Edge x₀ x₂)
    (h₀₁ : SSet.Edge.CompStruct a₀₁ b₀₁ e₀₁)
    (h₁₂ : SSet.Edge.CompStruct a₁₂ b₁₂ e₁₂)
    (h₀₂ : SSet.Edge.CompStruct a₀₂ b₀₂ e₀₂)
    {l₀ l₁ l₂ r₀ r₁ r₂ c₀ c₁ c₂ c₃ : K _⦋0⦌}
    (l₀₁ : K.Edge l₀ l₁) (l₁₂ : K.Edge l₁ l₂) (l₀₂ : K.Edge l₀ l₂)
    (r₀₁ : K.Edge r₀ r₁) (r₁₂ : K.Edge r₁ r₂) (r₀₂ : K.Edge r₀ r₂)
    (c₀₁ : K.Edge c₀ c₁) (c₁₃ : K.Edge c₁ c₃) (c₀₂ : K.Edge c₀ c₂)
    (c₂₃ : K.Edge c₂ c₃) (c₀₃ : K.Edge c₀ c₃)
    (hl : SSet.Edge.CompStruct l₀₁ l₁₂ l₀₂)
    (hr : SSet.Edge.CompStruct r₀₁ r₁₂ r₀₂)
    (hcl : SSet.Edge.CompStruct c₀₁ c₁₃ c₀₃)
    (hcu : SSet.Edge.CompStruct c₀₂ c₂₃ c₀₃)
    (hl₀₁ : l₀₁.edge = a₀₁.edge) (hl₀₂ : l₀₂.edge = a₀₂.edge)
    (hr₁₂ : r₁₂.edge = b₁₂.edge) (hr₀₂ : r₀₂.edge = b₀₂.edge)
    (hc₀₁ : c₀₁.edge = b₀₁.edge) (hc₁₃ : c₁₃.edge = a₁₂.edge)
    (hc₀₂ : c₀₂.edge = l₁₂.edge) (hc₂₃ : c₂₃.edge = r₀₁.edge) :
    Nonempty (SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂) := by
  let a' : K.Edge m₀₁ m₀₂ := l₁₂.ofEq
    (edge_target_eq_of_edge_eq l₀₁ a₀₁ hl₀₁)
    (edge_target_eq_of_edge_eq l₀₂ a₀₂ hl₀₂)
  let b' : K.Edge m₀₂ m₁₂ := r₀₁.ofEq
    (edge_source_eq_of_edge_eq r₀₂ b₀₂ hr₀₂)
    (edge_source_eq_of_edge_eq r₁₂ b₁₂ hr₁₂)
  let d : K.Edge m₀₁ m₁₂ := c₀₃.ofEq
    (edge_source_eq_of_edge_eq c₀₁ b₀₁ hc₀₁)
    (edge_target_eq_of_edge_eq c₁₃ a₁₂ hc₁₃)
  have hl' : SSet.Edge.CompStruct a₀₁ a' a₀₂ := hl.ofEq hl₀₁ rfl hl₀₂
  have hr' : SSet.Edge.CompStruct b' b₁₂ b₀₂ := hr.ofEq rfl hr₁₂ hr₀₂
  have hcl' : SSet.Edge.CompStruct b₀₁ a₁₂ d := hcl.ofEq hc₀₁ hc₁₃ rfl
  have hcu' : SSet.Edge.CompStruct a' b' d := hcu.ofEq hc₀₂ hc₂₃ rfl
  exact nonemptyCompStruct_paste_factorizations a₀₁ b₀₁ e₀₁ a₁₂ b₁₂ e₁₂
    a₀₂ b₀₂ e₀₂ a' b' h₀₁ h₁₂ h₀₂ hl' hr'
    ((SSet.HomotopyCategory.homMk_comp_homMk hcl').trans
      (SSet.HomotopyCategory.homMk_comp_homMk hcu').symm)

end SerrePositivity.KST.SConstruction
