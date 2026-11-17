module

public import SerrePositivity.EInfinity.Hammock.TwoSidedWeightedLeftRows
public import SerrePositivity.EInfinity.Hammock.TwoSidedThomasonNerveMap

/-!
# 元の二方向比較射の元の重み付き左比較による因子化

概要：元の重み付き左比較の後の既存の一方向 Thomason 比較は元の二方向比較射自身。
方針：元の全対角頂点・左右成分・底の全射を照合する。
規約：弱同値な代替の射へ置き換えず、元の三つの射の等式を証明する。
使われ方：DK9.5の比較射自身の弱同値性への接続。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.TwoSidedThomason
open CategoryTheory Opposite

variable {W : Type u} [Category.{u} W]
  (F : Wᵒᵖ ⥤ Cat.{u, u}) (G : W ⥤ Cat.{u, u})

lemma weightedLeft_simplex_factorization {n : ℕ} (e : ComposableArrows (labels F G n) n) :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.simplex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantProjection F ⋙ G)
      (TwoSidedWeightedLeft.simplex F (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.values G n) e) = simplex F G e := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

lemma weightedLeft_map_factorization :
    TwoSidedWeightedLeft.diagonalMap F G ≫
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantProjection F ⋙ G) = map F G := by
  ext n e
  exact weightedLeft_simplex_factorization F G e

end SerrePositivity.EInfinity.Hammock.TwoSidedThomason
