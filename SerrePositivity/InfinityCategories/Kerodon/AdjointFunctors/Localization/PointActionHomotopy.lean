module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.PointActions
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-!
# 元の点のホモトピーによる前後合成のホモトピー

概要：単位からの二写像のホモトピーを元の豊穣合成へ代入する。
方針：全次数の同じ区間パラメータと点の合成の自然性を使う。
規約：全語の余極限上で構成し、Kan 性は要求しない。
使われ方：指定射の前後合成のホモトピー逆。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {X Y Z : C}

def postcomposeHomotopyMap (X : C)
    {p q : 𝟙_ SSet.{max u v} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W Y Z} (H : SSet.Homotopy p q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y ⊗ SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Z where
  app n := ↾fun x => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W X Y Z x.1 (H.h.app n (PUnit.unit, x.2))
  naturality n m θ := by
    apply ConcreteCategory.hom_ext
    intro x
    have h := congrArg (fun k => k (PUnit.unit, x.2)) (H.h.naturality θ)
    change H.h.app m (PUnit.unit, (SSet.stdSimplex.obj (SimplexCategory.mk 1)).map θ x.2) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W Y Z).map θ (H.h.app n (PUnit.unit, x.2)) at h
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W X Y Z ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y).map θ x.1)
      (H.h.app m (PUnit.unit, (SSet.stdSimplex.obj (SimplexCategory.mk 1)).map θ x.2)) = _
    rw [h]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint_simplex W X Y Z θ x.1 (H.h.app n (PUnit.unit, x.2))

def postcomposeHomotopy (X : C)
    {p q : 𝟙_ SSet.{max u v} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W Y Z} (H : SSet.Homotopy p q) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap X p) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap X q) where
  h := postcomposeHomotopyMap X H
  h₀ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W X Y Z x ((SSet.ι₀ ≫ H.h).app n PUnit.unit) = _
    rw [H.h₀]
    rfl
  h₁ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W X Y Z x ((SSet.ι₁ ≫ H.h).app n PUnit.unit) = _
    rw [H.h₁]
    rfl
  rel := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

def precomposeHomotopyMap (Z : C)
    {p q : 𝟙_ SSet.{max u v} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y} (H : SSet.Homotopy p q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W Y Z ⊗ SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Z where
  app n := ↾fun x => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W X Y Z (H.h.app n (PUnit.unit, x.2)) x.1
  naturality n m θ := by
    apply ConcreteCategory.hom_ext
    intro x
    have h := congrArg (fun k => k (PUnit.unit, x.2)) (H.h.naturality θ)
    change H.h.app m (PUnit.unit, (SSet.stdSimplex.obj (SimplexCategory.mk 1)).map θ x.2) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y).map θ (H.h.app n (PUnit.unit, x.2)) at h
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W X Y Z
      (H.h.app m (PUnit.unit, (SSet.stdSimplex.obj (SimplexCategory.mk 1)).map θ x.2))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W Y Z).map θ x.1) = _
    rw [h]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint_simplex W X Y Z θ (H.h.app n (PUnit.unit, x.2)) x.1

def precomposeHomotopy (Z : C)
    {p q : 𝟙_ SSet.{max u v} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y} (H : SSet.Homotopy p q) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap p Z) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap q Z) where
  h := precomposeHomotopyMap Z H
  h₀ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W X Y Z ((SSet.ι₀ ≫ H.h).app n PUnit.unit) x = _
    rw [H.h₀]
    rfl
  h₁ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W X Y Z ((SSet.ι₁ ≫ H.h).app n PUnit.unit) x = _
    rw [H.h₁]
    rfl
  rel := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
