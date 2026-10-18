module

public import SerrePositivity.InfinityCategories.Coherent.IntervalFunctor
public import SerrePositivity.InfinityCategories.Coherent.HornCells

/-!
# ホーンの回収豊穣関手の再添字

概要：既知面からの回収の選択独立性と真部分区間での合成の整合性を準備する。
方針：閉区間への射影、ホーンの自然性、豊穣関手の構造則を使う。
規約：追加の充填仮定や局所 Kan 性を用いない。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8–2.4.5.9。
-/

@[expose] public section

universe v u w

open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Coherent

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]
variable {D : Type w} [EnrichedCategory SSet.{v} D]
/-- 概要：等しい豊穣関手を共通の対象族へ移した結果は等しい。
方針：豊穣関手の等式で置換し、所属の証明の一意性を使う。
規約：Mathlib の native な Path と共通の頂点対象を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8–2.4.5.9 の合成面の整合性。 -/
lemma reobjectFunctor_congr (F G : EnrichedFunctor SSet D C) (h : F = G)
    (g : D → C) (hF : ∀ x, F.obj x = g x) (hG : ∀ x, G.obj x = g x) :
    reobjectFunctor F g hF = reobjectFunctor G g hG := by
  subst G
  rfl
variable {J K L : Type v} [LinearOrder J] [LinearOrder K] [LinearOrder L]
/-- 概要：順序写像の合成に対する Hom 写像は再添字の合成である。
方針：thickening の豊穣関手の合成則を Hom で評価する。
規約：Mathlib の native な Path と共通の頂点対象を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8–2.4.5.9 の合成面の整合性。 -/
lemma thickeningFunctor_comp_map (f : J →o K) (g : K →o L)
    (x y : SimplicialThickening J) :
    (SimplicialThickening.functor (g.comp f)).map x y =
      (SimplicialThickening.functor f).map x y ≫
        (SimplicialThickening.functor g).map
          ((SimplicialThickening.functor f).obj x) ((SimplicialThickening.functor f).obj y) := by
  apply eq_of_heq
  have hm (F G : EnrichedFunctor SSet (SimplicialThickening J)
      (SimplicialThickening L)) (h : F = G) : HEq (F.map x y) (G.map x y) := by
    subst G
    rfl
  exact hm _ _ (SimplicialThickening.functor_comp f g)

set_option backward.isDefEq.respectTransparency false in
/-- 概要：面からの回収は任意の線形順序への再添字と可換である。
方針：共通対象と Hom の式を比較し、thickening の合成則を使う。
規約：Mathlib の native な Path と共通の頂点対象を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8–2.4.5.9 の合成面の整合性。 -/
lemma hornFunctorViaFace_comp {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (j : Fin (n + 3)) (hj : j ≠ i) (f : J →o ULift.{v} (Fin (n + 3)))
    (hf : ∀ x, (f x).down ≠ j) (e : K →o J) :
    (SimplicialThickening.functor e).comp SSet (hornFunctorViaFace σ j hj f hf) =
      hornFunctorViaFace σ j hj (f.comp e) (fun x ↦ hf (e x)) := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro x y
  simp only [EnrichedFunctor.comp_map, eqToHom_refl, Category.comp_id, hornFunctorViaFace_map]
  rw [thickeningFunctor_comp_map, Category.assoc]
  rfl
/-- 概要：同じ単体が二つの既知面を避ければ、両面からの回収豊穣関手は等しい。
方針：ホーン内の同じ単体の像の等式を共通の対象族へ移す。
規約：Mathlib の native な Path と共通の頂点対象を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8–2.4.5.9 の合成面の整合性。 -/
lemma hornFunctorViaFace_simplex_eq {m n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (θ : ⦋m⦌ ⟶ ⦋n + 2⦌) (j k : Fin (n + 3)) (hj : j ≠ i) (hk : k ≠ i)
    (hθj : ∀ a, θ.toOrderHom a ≠ j) (hθk : ∀ a, θ.toOrderHom a ≠ k) :
    hornFunctorViaFace σ j hj θ.toOrderHom.uliftMap (fun x ↦ hθj x.down) =
      hornFunctorViaFace σ k hk θ.toOrderHom.uliftMap (fun x ↦ hθk x.down) := by
  unfold hornFunctorViaFace
  apply reobjectFunctor_congr
  change (SimplicialNerve C).map θ.op
      ((SimplicialNerve C).map (faceRetraction j).op (σ.app _ (SSet.horn.face i j hj))) =
    (SimplicialNerve C).map θ.op
      ((SimplicialNerve C).map (faceRetraction k).op (σ.app _ (SSet.horn.face i k hk)))
  rw [← CategoryTheory.Functor.map_comp_apply, ← CategoryTheory.Functor.map_comp_apply,
    ← op_comp, ← op_comp, ← faceRetraction_factor, ← faceRetraction_factor]
  exact hornRestriction_independent i σ θ j k hj hk hθj hθk

end SerrePositivity.InfinityCategories.Coherent
