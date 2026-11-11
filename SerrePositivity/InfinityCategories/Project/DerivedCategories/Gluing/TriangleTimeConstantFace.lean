module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.FirstUnitCollarFamilies
/-! # 一定の三角形面の元端での回収

概要：時間に依らない指定辺を、同じ三角形族のどちらかの元端から回収する。
方針：区間端を評価し、時間因子を忘れる射影の同一性を使う。
規約：元端と実三角形を変えない。使われ方：native 可変辺を元 Hom 入力に同定する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
lemma dgGluingTriangleConstantFace_endpoint {K Z : SSet.{u}} (i : Fin 3) (j : Fin 2)
    (V : (Δ[2] : SSet.{u}) ⊗ (K ⊗ Δ[1]) ⟶ Z) (e : (Δ[1] : SSet.{u}) ⊗ K ⟶ Z)
    (h : (stdSimplex.δ i ▷ (K ⊗ Δ[1])) ≫ V =
      (Δ[1] ◁ fst K (Δ[1] : SSet.{u})) ≫ e) :
    e = (stdSimplex.δ i ▷ K) ≫
      (Δ[2] ◁ (if j = 0 then (ι₀ : K ⟶ _) else ι₁)) ≫ V := by
  calc
    _ = (Δ[1] ◁ (if j = 0 then (ι₀ : K ⟶ _) else ι₁)) ≫
        ((Δ[1] ◁ fst K (Δ[1] : SSet.{u})) ≫ e) := by
      fin_cases j <;> apply SSet.hom_ext <;> intro d <;>
        apply ConcreteCategory.hom_ext <;> intro a <;> rfl
    _ = (Δ[1] ◁ (if j = 0 then (ι₀ : K ⟶ _) else ι₁)) ≫
        ((stdSimplex.δ i ▷ (K ⊗ Δ[1])) ≫ V) := by rw [h]
    _ = _ := by
      fin_cases j <;> apply SSet.hom_ext <;> intro d <;>
        apply ConcreteCategory.hom_ext <;> intro a <;> rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
