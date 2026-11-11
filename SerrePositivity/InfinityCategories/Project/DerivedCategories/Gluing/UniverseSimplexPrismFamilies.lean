module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseCubeFamilies

/-! # 標準単体上の全区間族の宇宙輸送

概要：区間と標準単体の積の全族を、元パラメーターを保って共通宇宙へ移す。
方針：区間と標準単体の実宇宙同型を順に適用する。
規約：全単体・全区間評価と面への制限を保持する。
使われ方：標準合成三角形の augmentation prism を native 加群比較へ移す。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
variable {K X : SSet.{u}}

/-- 概要：標準単体の区間族の始域を元宇宙の積へ移す。
方針：二つの標準単体同型と積の同型を使う。
規約：区間を第一因子に保つ。使われ方：全 augmentation 三角形族の輸送。 -/
def dgGluingUliftSimplexPrismDomain (n : ℕ) (K : SSet.{u}) :
    (Δ[1] : SSet.{max u v}) ⊗ (Δ[n] ⊗ (SSet.uliftFunctor.{v, u}).obj K) ⟶
      (SSet.uliftFunctor.{v, u}).obj ((Δ[1] : SSet.{u}) ⊗ (Δ[n] ⊗ K)) :=
  (Δ[1] ◁ (((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} n).inv ▷ (SSet.uliftFunctor.{v, u}).obj K) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso (Δ[n] : SSet.{u}) K).inv)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftPrismDomain.{u, v} (Δ[n] ⊗ K)

/-- 概要：同じ標準単体上の全区間族を共通宇宙へ移す。
方針：実始域同型の後で元写像を ULift する。
規約：対象・Hom と二つのパラメーターを変えない。使われ方：native 合成 prism。 -/
def dgGluingUliftSimplexPrismFamily (n : ℕ)
    (h : (Δ[1] : SSet.{u}) ⊗ (Δ[n] ⊗ K) ⟶ X) :=
  dgGluingUliftSimplexPrismDomain.{u, v} n K ≫ (SSet.uliftFunctor.{v, u}).map h

lemma dgGluingUliftSimplexPrismFamily_one
    (h : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ K) ⟶ X) :
    dgGluingUliftSimplexPrismFamily.{u, v} 1 h = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSquareFamily.{u, v} h := rfl

lemma dgGluingUliftSimplexPrismFamily_face {n : ℕ}
    (h : (Δ[1] : SSet.{u}) ⊗ (Δ[n + 1] ⊗ K) ⟶ X) (i : Fin (n + 2)) :
    (Δ[1] ◁ (stdSimplex.δ i ▷ _)) ≫ dgGluingUliftSimplexPrismFamily.{u, v} (n + 1) h =
      dgGluingUliftSimplexPrismFamily.{u, v} n
        ((Δ[1] ◁ (stdSimplex.δ i ▷ K)) ≫ h) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

lemma dgGluingUliftSimplexPrismFamily_precomp {L : SSet.{u}} {n : ℕ}
    (h : (Δ[1] : SSet.{u}) ⊗ (Δ[n] ⊗ K) ⟶ X) (f : L ⟶ K) :
    (Δ[1] ◁ (Δ[n] ◁ (SSet.uliftFunctor.{v, u}).map f)) ≫
        dgGluingUliftSimplexPrismFamily.{u, v} n h =
      dgGluingUliftSimplexPrismFamily.{u, v} n ((Δ[1] ◁ (Δ[n] ◁ f)) ≫ h) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

lemma dgGluingUliftSimplexPrismFamily_post {Y : SSet.{u}} {n : ℕ}
    (h : (Δ[1] : SSet.{u}) ⊗ (Δ[n] ⊗ K) ⟶ X) (f : X ⟶ Y) :
    dgGluingUliftSimplexPrismFamily.{u, v} n h ≫ (SSet.uliftFunctor.{v, u}).map f =
      dgGluingUliftSimplexPrismFamily.{u, v} n (h ≫ f) := by
  simp only [dgGluingUliftSimplexPrismFamily, Functor.map_comp, Category.assoc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
