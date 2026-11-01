module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.FramedMappingBifunctor
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# 中断した任意モデル源への一般化：FramedResolutionChains

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Lift arbitrary finite composition chains using their actual frame maps。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0091][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0091
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Lift arbitrary finite composition chains using their actual frame maps

All longer arrows are composed in the framed category. Reindexing is done
on the lifted diagram itself; it never independently reselects its frames.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.HomotopyFunctionComplex.FramedResolution
variable {C : Type u} [Category.{v} C] [ModelCategory C] {n m : ℕ}

abbrev chainArrow (F : ComposableArrows (ResolutionObject C) n) (i : Fin n) :=
  F.map (homOfLE (Fin.castSucc_le_succ i))

/-- The supplied adjacent frame maps, rather than freshly chosen composite lifts, are used. -/
def liftChain (F : ComposableArrows (ResolutionObject C) n)
    (φ : ∀ i : Fin n, ResolutionLiftPrecomposition.FrameMap (chainArrow F i)) :
    ComposableArrows (FramedResolution C) n :=
  ComposableArrows.mkOfObjOfMapSucc (fun i => ofResolution (F.obj i))
    (fun i => ⟨chainArrow F i, (φ i).val, (φ i).property⟩)

@[simp]
lemma liftChain_obj (F : ComposableArrows (ResolutionObject C) n)
    (φ : ∀ i : Fin n, ResolutionLiftPrecomposition.FrameMap (chainArrow F i)) (i : Fin (n + 1)) :
    (liftChain F φ).obj i = ofResolution (F.obj i) := rfl

lemma liftChain_adjacent (F : ComposableArrows (ResolutionObject C) n)
    (φ : ∀ i : Fin n, ResolutionLiftPrecomposition.FrameMap (chainArrow F i))
    (i : ℕ) (hi : i < n) :
    (liftChain F φ).map' i (i + 1) =
      (⟨chainArrow F ⟨i, hi⟩, (φ ⟨i, hi⟩).val, (φ ⟨i, hi⟩).property⟩ :
        ofResolution (F.obj ⟨i, by omega⟩) ⟶ ofResolution (F.obj ⟨i + 1, by omega⟩)) :=
  ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi

lemma liftChain_forget (F : ComposableArrows (ResolutionObject C) n)
    (φ : ∀ i : Fin n, ResolutionLiftPrecomposition.FrameMap (chainArrow F i)) :
    liftChain F φ ⋙ forget = F := by
  refine ComposableArrows.ext (F := liftChain F φ ⋙ forget) (G := F) (fun _ => rfl) ?_
  intro i hi
  have h := congrArg (fun q => q.map) (liftChain_adjacent F φ i hi)
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change ((liftChain F φ).map' i (i + 1)).map = F.map' i (i + 1)
  exact h

/-- Every finite simplex lifts, with the objects and all original inner arrows retained. -/
lemma nerveForget_surjective (k : SimplexCategoryᵒᵖ) :
    Function.Surjective ((nerveMap (forget (C := C))).app k) := by
  intro F
  exact ⟨liftChain F (fun i => ResolutionLiftPrecomposition.lift (chainArrow F i)),
    liftChain_forget F _⟩

/-- Faces and degeneracies of an actual lifted chain project to the corresponding base chain. -/
lemma liftChain_reindex_forget (F : ComposableArrows (ResolutionObject C) n)
    (φ : ∀ i : Fin n, ResolutionLiftPrecomposition.FrameMap (chainArrow F i))
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    (θ.toOrderHom.monotone.functor ⋙ liftChain F φ) ⋙ forget =
      θ.toOrderHom.monotone.functor ⋙ F :=
  congrArg (fun G => θ.toOrderHom.monotone.functor ⋙ G) (liftChain_forget F φ)

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

/-- One contravariant diagram of target functors for an entire actual framed chain. -/
abbrev chainHom (F : ComposableArrows (FramedResolution C) n) :
    (Fin (n + 1))ᵒᵖ ⥤ C ⥤ SSet.{v} := F.op ⋙ hom hcof hfib

lemma chainHom_reindex (F : ComposableArrows (FramedResolution C) n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    chainHom hcof hfib (θ.toOrderHom.monotone.functor ⋙ F) =
      θ.toOrderHom.monotone.functor.op ⋙ chainHom hcof hfib F := rfl

lemma chainHom_composition (F : ComposableArrows (FramedResolution C) n)
    {i j k : (Fin (n + 1))ᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) (Z : C) :
    ((chainHom hcof hfib F).map (a ≫ b)).app Z =
      ((chainHom hcof hfib F).map a).app Z ≫ ((chainHom hcof hfib F).map b).app Z :=
  congr_app ((chainHom hcof hfib F).map_comp a b) Z

end SerrePositivity.HomotopyFunctionComplex.FramedResolution
