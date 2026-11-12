module

public import SerrePositivity.EInfinity.Hammock.LeftRoofPrefixCoreNaturality

/-!
# 元の roof 全円柱の始点変更への厳密な自然性

概要：Under.map に沿う制限は元の始点射による前合成と全円柱で一致する。
方針：三列への正規化・先頭二列の縮約・元の余極限の自然性を使う。
規約：端点やホモトピー類だけでなく同じ h の全単体を比較する。
使われ方：native roof の coherent 全三角形の合成条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.LeftRoof.Prefix
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
variable {C I : Type u} [Category.{u} C] [Category.{u} I]
  (W : MorphismProperty C) [W.IsMultiplicative]
  (U : I ⥤ C) {X Y : C} (p : U ⟶ (Functor.const I).obj X)
  (hp : ∀ i, W (p.app i)) (σ : U ⟶ (Functor.const I).obj Y)
  (hU : ∀ {i j} (a : i ⟶ j), W (U.map a)) (i : I)

lemma arrowHomotopy_h_core_app (n : SimplexCategoryᵒᵖ)
    (a : (nerve (Under i)).obj n) (t : (Δ[1] : SSet.{u}).obj n) :
    (arrowHomotopy W U p hp σ hU i).h.app n (a, t) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W (U.obj i) Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoof.word).app n
        (((stdSimplex.objEquiv t).toOrderHom.monotone.functor.prod' a) ⋙
          coreCylinder W U p hp σ hU i) := by
  rw [arrowHomotopy_h_app]
  let Γ := (stdSimplex.objEquiv t).toOrderHom.monotone.functor.prod' a
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion_naturality W (U.obj i) Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.lowerInsert) n)
      (Γ ⋙ coreCylinder W U p hp σ hU i)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W (U.obj i) Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.word).app n
    ((Γ ⋙ coreCylinder W U p hp σ hU i) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.lowerInsert) = _ at h
  rw [CategoryTheory.Functor.assoc, coreCylinder_insert] at h
  exact h

lemma arrowHomotopy_underMap {j : I} (a : i ⟶ j) :
    (nerveMap (Under.map a) ▷ (Δ[1] : SSet.{u})) ≫ (arrowHomotopy W U p hp σ hU i).h =
      (arrowHomotopy W U p hp σ hU j).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W (U.map a)) Y := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  rintro ⟨τ, t⟩
  change (arrowHomotopy W U p hp σ hU i).h.app n (τ ⋙ Under.map a, t) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W (U.obj i) (U.obj j) Y (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint W (U.map a) n)
      ((arrowHomotopy W U p hp σ hU j).h.app n (τ, t))
  rw [arrowHomotopy_h_core_app, arrowHomotopy_h_core_app, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint_inclusions]
  let Γ := (stdSimplex.objEquiv t).toOrderHom.monotone.functor.prod' τ
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion_naturality W (U.obj i) Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoofPrecompose.collapse) n)
      (Γ ⋙ corePrecomposeCylinder W U p hp σ hU i a)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W (U.obj i) Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoof.word).app n
    ((Γ ⋙ corePrecomposeCylinder W U p hp σ hU i a) ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardRoofPrecompose.collapse) = _ at h
  rw [CategoryTheory.Functor.assoc, coreCylinder_underMap] at h
  exact h

end SerrePositivity.EInfinity.Hammock.LeftRoof.Prefix
