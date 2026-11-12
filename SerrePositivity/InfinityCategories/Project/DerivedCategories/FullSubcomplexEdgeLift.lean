module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FullSubcomplexTriangleApexLift

/-! # 両端点を指定した実辺の全部分複体への持ち上げ

概要：両端点が全部分複体に入る実辺を、同じ両端点の型付き辺へ持ち上げる。
方針：一単体の二頂点を列挙し、指定両端点の所属を用いる。
規約：台の一単体を厳密に保つ。使われ方：固定した実 over 脚の分母部分複体への回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {X : SSet.{u}} (P : X _⦋0⦌ → Prop)

/-- 両端点条件から、元の実辺を同じ両端点の全部分複体辺へ持ち上げる。 -/
def fullSubcomplexEdgeLift
    (a b : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌)
    (σ : X _⦋1⦌) (hs : X.δ 1 σ = a.val) (ht : X.δ 0 σ = b.val) :
    Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet)) a b where
  edge := ⟨σ, by
    intro v
    generalize hi : v.toOrderHom 0 = i
    fin_cases i
    · have he : v = SimplexCategory.δ (1 : Fin 2) :=
        SimplexCategory.Hom.ext_zero_left _ _ hi
      rw [he]
      change P (X.δ 1 σ)
      rw [hs]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex a
    · have he : v = SimplexCategory.δ (0 : Fin 2) :=
        SimplexCategory.Hom.ext_zero_left _ _ hi
      rw [he]
      change P (X.δ 0 σ)
      rw [ht]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex b⟩
  src_eq := Subtype.ext hs
  tgt_eq := Subtype.ext ht

/-- 持ち上げた実辺の台は元の一単体そのもの。 -/
lemma fullSubcomplexEdgeLift_val
    (a b : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌)
    (σ : X _⦋1⦌) (hs : X.δ 1 σ = a.val) (ht : X.δ 0 σ = b.val) :
    (fullSubcomplexEdgeLift P a b σ hs ht).edge.val = σ := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
