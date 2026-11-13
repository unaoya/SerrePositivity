module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.UniverseTriangleTimeFamilies
/-! # 入力変更と標的写像を含む時間付き三角形族の輸送

概要：元入力の変更・共通宇宙への持ち上げ・正本関手の後合成をまとめて扱う。
方針：同じ時間付き族の輸送から固定辺・一定可変辺・両端評価を厳密に回収する。
規約：元の族と全パラメーターを保持する。使われ方：native の補正族を元入力 fiber へ供給する。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
variable {K Z : SSet.{u}} {P W : SSet.{max u v}}
def dgGluingTriangleTimeTransport (n : ℕ) (V : (Δ[n] : SSet.{u}) ⊗ (K ⊗ Δ[1]) ⟶ Z)
    (a : P ⟶ (SSet.uliftFunctor.{v, u}).obj K)
    (q : (SSet.uliftFunctor.{v, u}).obj Z ⟶ W) :=
  (Δ[n] ◁ (a ▷ Δ[1])) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftTriangleTimeFamily.{u, v} n V ≫ q
lemma dgGluingTriangleTimeTransport_fixed_edge (i : Fin 3)
    (V : (Δ[2] : SSet.{u}) ⊗ (K ⊗ Δ[1]) ⟶ Z)
    (e : (Δ[1] : SSet.{u}) ⟶ Z)
    (hV : (stdSimplex.δ i ▷ (K ⊗ Δ[1])) ≫ V =
      fst (Δ[1] : SSet.{u}) (K ⊗ Δ[1]) ≫ e)
    (a : P ⟶ (SSet.uliftFunctor.{v, u}).obj K)
    (q : (SSet.uliftFunctor.{v, u}).obj Z ⟶ W) :
    (stdSimplex.δ i ▷ (P ⊗ Δ[1])) ≫ dgGluingTriangleTimeTransport 2 V a q =
      fst (Δ[1] : SSet.{max u v}) (P ⊗ Δ[1]) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} 1).inv ≫ (SSet.uliftFunctor.{v, u}).map e ≫ q := by
  have hU := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftTriangleTimeFamily_fixed_edge.{u, v} i V e hV
  calc
    _ = (Δ[1] ◁ (a ▷ Δ[1])) ≫
        ((stdSimplex.δ i ▷ ((SSet.uliftFunctor.{v, u}).obj K ⊗ Δ[1])) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftTriangleTimeFamily.{u, v} 2 V) ≫ q := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro s
      rfl
    _ = (Δ[1] ◁ (a ▷ Δ[1])) ≫
        (fst (Δ[1] : SSet.{max u v}) ((SSet.uliftFunctor.{v, u}).obj K ⊗ Δ[1]) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} 1).inv ≫ (SSet.uliftFunctor.{v, u}).map e) ≫ q := by rw [hU]
    _ = _ := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro s
      rfl
lemma dgGluingTriangleTimeTransport_constant_edge (i : Fin 3)
    (V : (Δ[2] : SSet.{u}) ⊗ (K ⊗ Δ[1]) ⟶ Z)
    (e : (Δ[1] : SSet.{u}) ⊗ K ⟶ Z)
    (hV : (stdSimplex.δ i ▷ (K ⊗ Δ[1])) ≫ V =
      (Δ[1] ◁ fst K (Δ[1] : SSet.{u})) ≫ e)
    (a : P ⟶ (SSet.uliftFunctor.{v, u}).obj K)
    (q : (SSet.uliftFunctor.{v, u}).obj Z ⟶ W) :
    (stdSimplex.δ i ▷ (P ⊗ Δ[1])) ≫ dgGluingTriangleTimeTransport 2 V a q =
      (Δ[1] ◁ fst P (Δ[1] : SSet.{max u v})) ≫
        (Δ[1] ◁ a) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexFamily.{u, v} 1 e ≫ q := by
  have hU := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftTriangleTimeFamily_constant_edge.{u, v} i V e hV
  calc
    _ = (Δ[1] ◁ (a ▷ Δ[1])) ≫
        ((stdSimplex.δ i ▷ ((SSet.uliftFunctor.{v, u}).obj K ⊗ Δ[1])) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftTriangleTimeFamily.{u, v} 2 V) ≫ q := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro s
      rfl
    _ = (Δ[1] ◁ (a ▷ Δ[1])) ≫
        ((Δ[1] ◁ fst ((SSet.uliftFunctor.{v, u}).obj K) (Δ[1] : SSet.{max u v})) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexFamily.{u, v} 1 e) ≫ q := by rw [hU]
    _ = _ := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro s
      rfl
lemma dgGluingTriangleTimeTransport_endpoint (n : ℕ) (j : Fin 2)
    (V : (Δ[n] : SSet.{u}) ⊗ (K ⊗ Δ[1]) ⟶ Z)
    (a : P ⟶ (SSet.uliftFunctor.{v, u}).obj K)
    (q : (SSet.uliftFunctor.{v, u}).obj Z ⟶ W) :
    (Δ[n] ◁ (if j = 0 then (ι₀ : P ⟶ _) else ι₁)) ≫ dgGluingTriangleTimeTransport n V a q =
      (Δ[n] ◁ a) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexFamily.{u, v} n
        ((Δ[n] ◁ (if j = 0 then (ι₀ : K ⟶ _) else ι₁)) ≫ V) ≫ q := by
  calc
    _ = (Δ[n] ◁ a) ≫
        ((Δ[n] ◁ (if j = 0 then (ι₀ : (SSet.uliftFunctor.{v, u}).obj K ⟶ _) else ι₁)) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftTriangleTimeFamily.{u, v} n V) ≫ q := by
      fin_cases j <;> apply SSet.hom_ext <;> intro d <;>
        apply ConcreteCategory.hom_ext <;> intro s <;> rfl
    _ = _ := by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftTriangleTimeFamily_endpoint]


lemma dgGluingTriangleTimeTransport_endpoint_congr (n : ℕ) (j : Fin 2)
    (V V' : (Δ[n] : SSet.{u}) ⊗ (K ⊗ Δ[1]) ⟶ Z)
    (h : (Δ[n] ◁ (if j = 0 then (ι₀ : K ⟶ _) else ι₁)) ≫ V =
      (Δ[n] ◁ (if j = 0 then (ι₀ : K ⟶ _) else ι₁)) ≫ V')
    (a : P ⟶ (SSet.uliftFunctor.{v, u}).obj K)
    (q : (SSet.uliftFunctor.{v, u}).obj Z ⟶ W) :
    (Δ[n] ◁ (if j = 0 then (ι₀ : P ⟶ _) else ι₁)) ≫ dgGluingTriangleTimeTransport n V a q =
      (Δ[n] ◁ (if j = 0 then (ι₀ : P ⟶ _) else ι₁)) ≫ dgGluingTriangleTimeTransport n V' a q := by
  rw [dgGluingTriangleTimeTransport_endpoint, dgGluingTriangleTimeTransport_endpoint, h]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
