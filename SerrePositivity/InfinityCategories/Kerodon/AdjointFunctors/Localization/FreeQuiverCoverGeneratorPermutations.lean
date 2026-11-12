module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverLiftFibers
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiberSwap

/-!
# 元の生成矢の持ち上げによる持ち上げ射の集合の置換

概要：元の生成矢の持ち上げを全持ち上げ射の集合の置換に拡張する。
方針：元のファイバーの同値を全体の置換へ移し、元の生成矢上の作用を回収する。
規約：持ち上げ射そのものを右合成で送る。
使われ方：自由 groupoid 間の射影の忠実性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q)

def generatorPermutation :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∀ (S : Quiver.FreeGroupoid (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)) {B E : Q} (_ : B ⟶ E), Equiv.Perm (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LiftStar A S) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  intro S B E f
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fiberSwap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LiftFiber A S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.liftFiberEquiv A S f)

lemma generatorPermutation_forward :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∀ (S : Quiver.FreeGroupoid (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)) {x y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A} (f : x ⟶ y)
      (h : S ⟶ (Quiver.FreeGroupoid.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).obj x),
      generatorPermutation A S f.val (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.encodeStar A S _ h) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.encodeStar A S _ (h ≫ (Quiver.FreeGroupoid.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).map f) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  intro S x y f h
  rcases x with ⟨B, β⟩
  rcases y with ⟨E, γ⟩
  rcases f with ⟨f, hf⟩
  change B ⟶ E at f
  change β ≫ (Quiver.FreeGroupoid.of Q).map f = γ at hf
  subst γ
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fiberSwap_apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LiftFiber A S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.liftFiberEquiv A S f) ⟨β, h⟩

lemma generatorPermutation_backward :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∀ (S : Quiver.FreeGroupoid (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)) {x y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A} (f : x ⟶ y)
      (h : S ⟶ (Quiver.FreeGroupoid.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).obj y),
      (generatorPermutation A S f.val).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.encodeStar A S _ h) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.encodeStar A S _ (h ≫ inv ((Quiver.FreeGroupoid.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).map f)) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  intro S x y f h
  apply (generatorPermutation A S f.val).injective
  rw [Equiv.apply_symm_apply]
  have hf := generatorPermutation_forward A S f
    (h ≫ inv ((Quiver.FreeGroupoid.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).map f))
  have hc : (h ≫ inv ((Quiver.FreeGroupoid.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).map f)) ≫
      (Quiver.FreeGroupoid.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).map f = h := by
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact (hf.trans (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.encodeStar A S _) hc)).symm

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
