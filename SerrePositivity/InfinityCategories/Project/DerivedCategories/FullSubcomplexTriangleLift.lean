module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FullSubcomplexEdgeLift

/-! # 全部分複体への指定合成三角形の持ち上げ

概要：三つの指定辺を保つ元の圏の二単体を、同じ三辺の全部分複体内の二単体へ上げる。
方針：三頂点の条件を検査し、全部分型の外延性で全三面を照合する。
規約：充填を選び直さず指定二単体を保持。使われ方：実分母上の始錐の整合性。
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
variable {a b c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌}
variable (e₀₁ : Truncated.Edge (X := (truncation 2).obj
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u})) a b)
variable (e₁₂ : Truncated.Edge (X := (truncation 2).obj
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u})) b c)
variable (e₀₂ : Truncated.Edge (X := (truncation 2).obj
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u})) a c)
variable (T : Truncated.Edge.CompStruct
  (e₀₁.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι))
  (e₁₂.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι))
  (e₀₂.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι)))

/-- 指定三辺の合成三角形は、元の二単体を保ったまま全部分複体へ上がる。 -/
def fullSubcomplexTriangleLift : Truncated.Edge.CompStruct e₀₁ e₁₂ e₀₂ := by
  let ρ : X _⦋2⦌ := T.simplex
  have h₂ : X.δ 2 ρ = (e₀₁.edge).val := T.d₂
  have h₀ : X.δ 0 ρ = (e₁₂.edge).val := T.d₀
  have hv : ∀ v : ⦋0⦌ ⟶ ⦋2⦌, P (X.map v.op ρ) := by
    intro v
    generalize hi : v.toOrderHom 0 = i
    fin_cases i
    · have he : v = SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ (2 : Fin 3) :=
        SimplexCategory.Hom.ext_zero_left _ _ hi
      rw [he, op_comp, Functor.map_comp_apply]
      have hh : X.δ 1 (X.δ 2 ρ) = a.val :=
        (congrArg (fun e : X _⦋1⦌ => X.δ 1 e) h₂).trans
          (congrArg Subtype.val e₀₁.src_eq)
      exact hh ▸ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex a
    · have he : v = SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ (2 : Fin 3) :=
        SimplexCategory.Hom.ext_zero_left _ _ hi
      rw [he, op_comp, Functor.map_comp_apply]
      have hh : X.δ 0 (X.δ 2 ρ) = b.val :=
        (congrArg (fun e : X _⦋1⦌ => X.δ 0 e) h₂).trans
          (congrArg Subtype.val e₀₁.tgt_eq)
      exact hh ▸ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex b
    · have he : v = SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ (0 : Fin 3) :=
        SimplexCategory.Hom.ext_zero_left _ _ hi
      rw [he, op_comp, Functor.map_comp_apply]
      have hh : X.δ 0 (X.δ 0 ρ) = c.val :=
        (congrArg (fun e : X _⦋1⦌ => X.δ 0 e) h₀).trans
          (congrArg Subtype.val e₁₂.tgt_eq)
      exact hh ▸ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex c
  exact {
    simplex := ⟨ρ, hv⟩
    d₂ := Subtype.ext h₂
    d₀ := Subtype.ext h₀
    d₁ := Subtype.ext T.d₁ }

/-- 全部分複体に持ち上げた三角形の台は、元の指定二単体そのもの。 -/
lemma fullSubcomplexTriangleLift_simplex :
    (fullSubcomplexTriangleLift P e₀₁ e₁₂ e₀₂ T).simplex.val = T.simplex := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
