module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.FullSubcomplexTriangleApexLift

/-! # 指定零面を持つ実二単体からの始点と二脚の回収

概要：実二単体の零面が指定辺なら、元の始頂点・両端への実脚・合成二単体を回収する。
方針：三つの simplicial identity で端点を合わせ、元の二単体をそのまま使う。
規約：元の辺と全二単体を保つ。使われ方：実分母部分圏内の細分された辺錐。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {X : SSet.{u}} {b c : X _⦋0⦌}

/-- 指定零面を持つ実三角形の始頂点。 -/
def triangleConeApex (T : X _⦋2⦌) : X _⦋0⦌ := X.δ 1 (X.δ 1 T)

/-- 元の始頂点から、指定零面の始点への実脚。 -/
def triangleConeLegSource (T : X _⦋2⦌)
    (e : Truncated.Edge (X := (truncation 2).obj X) b c) (h₀ : X.δ 0 T = e.edge) :
    Truncated.Edge (X := (truncation 2).obj X) (triangleConeApex T) b where
  edge := X.δ 2 T
  src_eq := ConcreteCategory.congr_hom
    (SimplicialObject.δ_comp_δ X (i := (1 : Fin 2)) (j := (1 : Fin 2)) (by decide)) T
  tgt_eq := (ConcreteCategory.congr_hom
    (SimplicialObject.δ_comp_δ X (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)) T).trans
      ((congrArg (X.δ (1 : Fin 2)) h₀).trans e.src_eq)

/-- 同じ始頂点から、指定零面の終点への実脚。 -/
def triangleConeLegTarget (T : X _⦋2⦌)
    (e : Truncated.Edge (X := (truncation 2).obj X) b c) (h₀ : X.δ 0 T = e.edge) :
    Truncated.Edge (X := (truncation 2).obj X) (triangleConeApex T) c where
  edge := X.δ 1 T
  src_eq := rfl
  tgt_eq := (ConcreteCategory.congr_hom
    (SimplicialObject.δ_comp_δ X (i := (0 : Fin 2)) (j := (0 : Fin 2)) (by decide)) T).trans
      ((congrArg (X.δ (0 : Fin 2)) h₀).trans e.tgt_eq)

/-- 元の二単体は、回収した二脚と指定辺の同じ実合成二単体。 -/
def triangleConeCompStruct (T : X _⦋2⦌)
    (e : Truncated.Edge (X := (truncation 2).obj X) b c) (h₀ : X.δ 0 T = e.edge) :
    Truncated.Edge.CompStruct (triangleConeLegSource T e h₀) e (triangleConeLegTarget T e h₀) :=
  ⟨T, rfl, h₀, rfl⟩

/-- 回収した二脚の合成二単体の台は、元の実二単体そのもの。 -/
lemma triangleConeCompStruct_simplex (T : X _⦋2⦌)
    (e : Truncated.Edge (X := (truncation 2).obj X) b c) (h₀ : X.δ 0 T = e.edge) :
    (triangleConeCompStruct T e h₀).simplex = T := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
