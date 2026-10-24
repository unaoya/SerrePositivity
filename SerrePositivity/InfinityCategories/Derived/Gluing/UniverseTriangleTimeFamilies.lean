module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseSimplexPrismFamilies
public import SerrePositivity.InfinityCategories.Derived.Gluing.LastUnitCollarFamilies
/-! # 固定辺と時間を保つ三角形族の宇宙輸送

概要：全入力と時間を持つ三角形族を、固定辺・一定の可変辺・元端を保って共通宇宙へ移す。
方針：標準単体と積の宇宙同型を順に適用し、同じ単体を持ち上げる。
規約：両単位補正の再添字も厳密に保存し、対象の Small 性を要求しない。
使われ方：実入力固定変形を native 正本の導来比較へ輸送する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet HomotopyLimits
open scoped Simplicial
def dgGluingUliftTriangleTimeDomain (n : ℕ) (K : SSet.{u}) :
    (Δ[n] : SSet.{max u v}) ⊗ ((SSet.uliftFunctor.{v,u}).obj K ⊗ Δ[1]) ⟶
      (SSet.uliftFunctor.{v,u}).obj ((Δ[n] : SSet.{u}) ⊗ (K ⊗ Δ[1])) :=
  (Δ[n] ◁ (((SSet.uliftFunctor.{v,u}).obj K ◁ (uliftStdSimplexIso.{u,v} 1).inv) ≫
    (uliftTensorIso K (Δ[1] : SSet.{u})).inv)) ≫
      ((uliftStdSimplexIso.{u,v} n).inv ▷ (SSet.uliftFunctor.{v,u}).obj (K ⊗ Δ[1])) ≫
        (uliftTensorIso (Δ[n] : SSet.{u}) (K ⊗ Δ[1])).inv
def dgGluingUliftTriangleTimeFamily {K Z : SSet.{u}} (n : ℕ)
    (V : (Δ[n] : SSet.{u}) ⊗ (K ⊗ Δ[1]) ⟶ Z) :=
  dgGluingUliftTriangleTimeDomain.{u,v} n K ≫ (SSet.uliftFunctor.{v,u}).map V
lemma dgGluingUliftTriangleTimeFamily_fixed_edge {K Z : SSet.{u}} (i : Fin 3)
    (V : (Δ[2] : SSet.{u}) ⊗ (K ⊗ Δ[1]) ⟶ Z) (e : (Δ[1] : SSet.{u}) ⟶ Z)
    (hV : (stdSimplex.δ i ▷ (K ⊗ Δ[1])) ≫ V =
      fst (Δ[1] : SSet.{u}) (K ⊗ Δ[1]) ≫ e) :
    (stdSimplex.δ i ▷ ((SSet.uliftFunctor.{v,u}).obj K ⊗ Δ[1])) ≫
      dgGluingUliftTriangleTimeFamily.{u,v} 2 V =
    fst (Δ[1] : SSet.{max u v}) ((SSet.uliftFunctor.{v,u}).obj K ⊗ Δ[1]) ≫
      (uliftStdSimplexIso.{u,v} 1).inv ≫ (SSet.uliftFunctor.{v,u}).map e := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  apply ULift.ext
  let b : ((Δ[1] : SSet.{u}) ⊗ (K ⊗ Δ[1])).obj n :=
    (((uliftStdSimplexIso.{u,v} 1).inv.app n a.1).down,
      (a.2.1.down, ((uliftStdSimplexIso.{u,v} 1).inv.app n a.2.2).down))
  have h := congrArg (fun g : (Δ[1] : SSet.{u}) ⊗ (K ⊗ Δ[1]) ⟶ Z => g.app n b) hV
  exact h


lemma dgGluingUliftTriangleTimeFamily_constant_edge {K Z : SSet.{u}} (i : Fin 3)
    (V : (Δ[2] : SSet.{u}) ⊗ (K ⊗ Δ[1]) ⟶ Z)
    (e : (Δ[1] : SSet.{u}) ⊗ K ⟶ Z)
    (hV : (stdSimplex.δ i ▷ (K ⊗ Δ[1])) ≫ V =
      (Δ[1] ◁ fst K (Δ[1] : SSet.{u})) ≫ e) :
    (stdSimplex.δ i ▷ ((SSet.uliftFunctor.{v,u}).obj K ⊗ Δ[1])) ≫
      dgGluingUliftTriangleTimeFamily.{u,v} 2 V =
    (Δ[1] ◁ fst ((SSet.uliftFunctor.{v,u}).obj K) (Δ[1] : SSet.{max u v})) ≫
      dgGluingUliftSimplexFamily.{u,v} 1 e := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  apply ULift.ext
  let b : ((Δ[1] : SSet.{u}) ⊗ (K ⊗ Δ[1])).obj n :=
    (((uliftStdSimplexIso.{u,v} 1).inv.app n a.1).down,
      (a.2.1.down, ((uliftStdSimplexIso.{u,v} 1).inv.app n a.2.2).down))
  exact congrArg (fun g : (Δ[1] : SSet.{u}) ⊗ (K ⊗ Δ[1]) ⟶ Z => g.app n b) hV
lemma dgGluingUliftTriangleTimeFamily_endpoint {K Z : SSet.{u}} (n : ℕ)
    (V : (Δ[n] : SSet.{u}) ⊗ (K ⊗ Δ[1]) ⟶ Z) (j : Fin 2) :
    (Δ[n] ◁ (if j=0 then (ι₀ : (SSet.uliftFunctor.{v,u}).obj K ⟶ _) else ι₁)) ≫
      dgGluingUliftTriangleTimeFamily.{u,v} n V =
    dgGluingUliftSimplexFamily.{u,v} n
      ((Δ[n] ◁ (if j=0 then (ι₀ : K ⟶ _) else ι₁)) ≫ V) := by
  fin_cases j <;> apply SSet.hom_ext <;> intro d <;>
    apply ConcreteCategory.hom_ext <;> intro a <;> rfl
lemma dgGluingUliftTriangleTimeFamily_first_reindex {K Z : SSet.{u}}
    (T : (Δ[1] : SSet.{u}) ⊗ (Δ[2] ⊗ K) ⟶ Z) :
    dgGluingUliftTriangleTimeFamily.{u,v} 2
      (dgGluingTriangleTimeReindex dgGluingFirstUnitCollar ≫ T) =
      dgGluingTriangleTimeReindex dgGluingFirstUnitCollar ≫
        dgGluingUliftSimplexPrismFamily.{u,v} 2 T := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl
lemma dgGluingUliftTriangleTimeFamily_last_reindex {K Z : SSet.{u}}
    (T : (Δ[1] : SSet.{u}) ⊗ (Δ[2] ⊗ K) ⟶ Z) :
    dgGluingUliftTriangleTimeFamily.{u,v} 2
      (dgGluingTriangleTimeReindex dgGluingLastUnitCollar ≫ T) =
      dgGluingTriangleTimeReindex dgGluingLastUnitCollar ≫
        dgGluingUliftSimplexPrismFamily.{u,v} 2 T := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl


lemma dgGluingUliftTriangleTimeFamily_precomp {K L Z : SSet.{u}} (n : ℕ)
    (V : (Δ[n] : SSet.{u}) ⊗ (K ⊗ Δ[1]) ⟶ Z) (f : L ⟶ K) :
    (Δ[n] ◁ ((SSet.uliftFunctor.{v,u}).map f ▷ (Δ[1] : SSet.{max u v}))) ≫
      dgGluingUliftTriangleTimeFamily.{u,v} n V =
    dgGluingUliftTriangleTimeFamily.{u,v} n ((Δ[n] ◁ (f ▷ Δ[1])) ≫ V) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl
lemma dgGluingUliftTriangleTimeFamily_post {K Z W : SSet.{u}} (n : ℕ)
    (V : (Δ[n] : SSet.{u}) ⊗ (K ⊗ Δ[1]) ⟶ Z) (f : Z ⟶ W) :
    dgGluingUliftTriangleTimeFamily.{u,v} n V ≫ (SSet.uliftFunctor.{v,u}).map f =
    dgGluingUliftTriangleTimeFamily.{u,v} n (V ≫ f) := by
  simp only [dgGluingUliftTriangleTimeFamily, Functor.map_comp, Category.assoc]
end SerrePositivity.InfinityCategories
