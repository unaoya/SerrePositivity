module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexInvertingPullback

/-!
概要：単体圏の射列を、単体作用素の列と最初の単体から復元する。
方針：始点から各頂点への作用素で最初の単体を制限する。
規約：作用素の列に単射性や非退化性を仮定しない。
使われ方：一般のセル付加で単体圏の nerve の貼り合わせを検証する。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 底の単体の値を忘れ、次数と単体作用素だけを残す。 -/
def transportSimplexShapeFunctor (B : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B ⥤ SimplexCategoryᵒᵖ where
  obj s := s.objDown.obj
  map f := f.down.hom

/-- 形への忘却は、指定された両端の間の射を忠実に記録する。 -/
instance transportSimplexShapeFunctor_faithful (B : SSet.{u}) :
    (transportSimplexShapeFunctor B).Faithful where
  map_injective h := by
    apply ULift.ext
    exact CategoryTheory.Functor.Elements.Hom.ext h

/-- 単体圏の射列の、単体作用素の列としての形。 -/
def transportSimplexChainShape {B : SSet.{u}} {n : ℕ}
    (σ : ComposableArrows (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B) n) :
    ComposableArrows SimplexCategoryᵒᵖ n := σ ⋙ transportSimplexShapeFunctor B

/-- 作用素の列と最初の単体から、実際の単体圏の射列を作る。 -/
def transportSimplexChainFromShape {B : SSet.{u}} {n : ℕ}
    (τ : ComposableArrows SimplexCategoryᵒᵖ n) (b : B.obj (τ.obj 0)) :
    ComposableArrows (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B) n where
  obj i := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (B.map (τ.map (homOfLE (Fin.zero_le i))) b)
  map {i j} f := ⟨{ hom := τ.map f
                    map_val := by
                      change B.map (τ.map f)
                        (B.map (τ.map (homOfLE (Fin.zero_le i))) b) =
                          B.map (τ.map (homOfLE (Fin.zero_le j))) b
                      rw [← B.map_comp_apply, ← τ.map_comp]
                      rfl }⟩
  map_id i := by
    apply ULift.ext
    apply CategoryTheory.Functor.Elements.Hom.ext
    exact τ.map_id i
  map_comp f g := by
    apply ULift.ext
    apply CategoryTheory.Functor.Elements.Hom.ext
    exact τ.map_comp f g

/-- 復元した射列の形は、指定された作用素の列そのもの。 -/
lemma transportSimplexChainFromShape_shape {B : SSet.{u}} {n : ℕ}
    (τ : ComposableArrows SimplexCategoryᵒᵖ n) (b : B.obj (τ.obj 0)) :
    transportSimplexChainShape (transportSimplexChainFromShape τ b) = τ := rfl

/-- 復元した射列の最初の単体は、指定された単体に等しい。 -/
lemma transportSimplexChainFromShape_first {B : SSet.{u}} {n : ℕ}
    (τ : ComposableArrows SimplexCategoryᵒᵖ n) (b : B.obj (τ.obj 0)) :
    ((transportSimplexChainFromShape τ b).obj 0).objDown.val = b := by
  change B.map (τ.map (𝟙 _)) b = b
  rw [τ.map_id, B.map_id_apply]

/-- 射列の形と最初の単体による復元は、各対象で元の単体に戻る。 -/
lemma transportSimplexChainFromShape_obj_recover {B : SSet.{u}} {n : ℕ}
    (σ : ComposableArrows (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B) n) (i : Fin (n + 1)) :
    (transportSimplexChainFromShape (transportSimplexChainShape σ)
      (σ.obj 0).objDown.val).obj i = σ.obj i := by
  change B.elementsMk _ (B.map (σ.map (homOfLE (Fin.zero_le i))).down.hom
    (σ.obj 0).objDown.val) = (σ.obj i).objDown
  refine CategoryTheory.Functor.Elements.ext _ _ rfl ?_
  change B.map (𝟙 _) (B.map (σ.map (homOfLE (Fin.zero_le i))).down.hom
    (σ.obj 0).objDown.val) = (σ.obj i).objDown.val
  rw [B.map_id_apply]
  exact (σ.map (homOfLE (Fin.zero_le i))).down.map_val

/-- 形と最初の単体から元の射列全体を厳密に復元する。 -/
lemma transportSimplexChainFromShape_recover {B : SSet.{u}} {n : ℕ}
    (σ : ComposableArrows (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B) n) :
    transportSimplexChainFromShape (transportSimplexChainShape σ)
      (σ.obj 0).objDown.val = σ := by
  refine CategoryTheory.Functor.ext (transportSimplexChainFromShape_obj_recover σ)
    (fun i j f ↦ ?_)
  apply (transportSimplexShapeFunctor B).map_injective
  simp only [CategoryTheory.Functor.map_comp, eqToHom_map,
    eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- 射列の各次数は、作用素の列と最初の単体の依存和と全単射。 -/
def transportSimplexChainEquiv (B : SSet.{u}) (n : ℕ) :
    ComposableArrows (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B) n ≃
      Σ τ : ComposableArrows SimplexCategoryᵒᵖ n, B.obj (τ.obj 0) where
  toFun σ := ⟨transportSimplexChainShape σ, (σ.obj 0).objDown.val⟩
  invFun s := transportSimplexChainFromShape s.1 s.2
  left_inv := transportSimplexChainFromShape_recover
  right_inv s := by
    rcases s with ⟨τ, b⟩
    exact congrArg (fun x : B.obj (τ.obj 0) ↦
      (⟨τ, x⟩ : Σ τ : ComposableArrows SimplexCategoryᵒᵖ n, B.obj (τ.obj 0)))
        (transportSimplexChainFromShape_first τ b)

/-- 形と最初の単体による座標は、底の任意の射と厳密に可換。 -/
lemma transportSimplexChainEquiv_naturality {B D : SSet.{u}} (f : B ⟶ D) {n : ℕ}
    (σ : ComposableArrows (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B) n) :
    transportSimplexChainEquiv D n (σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor f) =
      Sigma.map id (fun τ b ↦ f.app (τ.obj 0) b) (transportSimplexChainEquiv B n σ) := rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
