module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockMap
public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockComparison
public import SerrePositivity.EInfinity.SimplicialLocalization.EnrichedMap

/-!
# 元の自由 hammock の右比較の係数自然性

概要：元の zigzag の局所化評価と実際の DK Hom の係数写像を照合する。
方針：元の Q の自然性と全端点移送を同じ値の等式で相殺する。
規約：全語・全次数と元の右比較射を保持する。
使われ方：DK と hammock の高次比較の係数自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory CategoryTheory.Limits Hammock
variable {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (F : C ⟶ D)

lemma freeHammockValue_map (X Y : C.category) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (n : SimplexCategoryᵒᵖ)
    (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag ((freeResolution C).obj n).weakEquivalences w
      (freeResolutionObject C n X) (freeResolutionObject C n Y)) :
    (freeHammockLocalizationObjects D).value n
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor ((freeResolutionMap F).app n)
          (freeResolutionMap_object F n X) (freeResolutionMap_object F n Y)).obj S) =
      (localizationHomMap F X Y).app n ((freeHammockLocalizationObjects C).value n S) := by
  change (freeHammockLocalizationObjects D).value n _ =
    eqToHom (localizedFreeResolutionMap_object F n X).symm ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap ((freeResolutionMap F).app n)).map
        ((freeHammockLocalizationObjects C).value n S) ≫
          eqToHom (localizedFreeResolutionMap_object F n Y)
  apply eq_of_heq
  dsimp only [FixedObjectDiagram.LocalizationObjects.value]
  simp only [Functor.map_comp, eqToHom_map, eqToHom_comp_heq_iff,
    comp_eqToHom_heq_iff, heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.value_fixed_comparison ((freeResolutionMap F).app n)
    ((freeResolution C).obj n).weakEquivalences.Q
    ((freeResolution C).obj n).weakEquivalences.Q_inverts
    ((freeResolution D).obj n).weakEquivalences.Q
    ((freeResolution D).obj n).weakEquivalences.Q_inverts
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap ((freeResolutionMap F).app n))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap_fac ((freeResolutionMap F).app n))
    (freeResolutionMap_object F n X) (freeResolutionMap_object F n Y) S

lemma freeHammockGraphMap_comparison (X Y : C.category) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word)
    (n : SimplexCategoryᵒᵖ) :
    ((freeHammockWordMap F X Y).app w).app n ≫
        (freeHammockLocalizationObjects D).graphValue n w (F.functor.obj X) (F.functor.obj Y) =
      (freeHammockLocalizationObjects C).graphValue n w X Y ≫
        (Functor.const SimplexCategoryᵒᵖ).map ((localizationHomMap F X Y).app n) := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro σ
  exact freeHammockValue_map F X Y w n (σ.obj 0)

lemma freeHammockMap_comparison (X Y : C.category) :
    freeHammockMap F X Y ≫
        freeHammockHomComparison D (F.functor.obj X) (F.functor.obj Y) =
      freeHammockHomComparison C X Y ≫
        Functor.whiskerRight (localizationHomMap F X Y) (Functor.const SimplexCategoryᵒᵖ) := by
  apply NatTrans.ext
  funext n
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph_hom_ext ((freeResolution C).obj n).weakEquivalences
    (freeResolutionObject C n X) (freeResolutionObject C n Y)
  intro w
  have hι := NatTrans.congr_app (freeHammockMap_inclusion F X Y w) n
  change ((freeHammockWordMap F X Y).app w).app n ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion ((freeResolution D).obj n).weakEquivalences
        (freeResolutionObject D n (F.functor.obj X))
        (freeResolutionObject D n (F.functor.obj Y)) w =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion ((freeResolution C).obj n).weakEquivalences
      (freeResolutionObject C n X) (freeResolutionObject C n Y) w ≫
        (freeHammockMap F X Y).app n at hι
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion _ _ _ w ≫
      ((freeHammockMap F X Y).app n ≫
        (freeHammockHomComparison D (F.functor.obj X) (F.functor.obj Y)).app n) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion _ _ _ w ≫ ((freeHammockHomComparison C X Y).app n ≫
      (Functor.const SimplexCategoryᵒᵖ).map ((localizationHomMap F X Y).app n))
  rw [← Category.assoc, ← hι, Category.assoc, freeHammockHomComparison_fac,
    freeHammockGraphMap_comparison, ← Category.assoc, freeHammockHomComparison_fac]

lemma freeHammockDiagonalMap_comparison (X Y : C.category) :
    freeHammockDiagonalMap F X Y ≫
        freeHammockDiagonalComparison D (F.functor.obj X) (F.functor.obj Y) =
      freeHammockDiagonalComparison C X Y ≫ localizationHomMap F X Y := by
  apply NatTrans.ext
  funext n
  exact NatTrans.congr_app (NatTrans.congr_app (freeHammockMap_comparison F X Y) n) n

end SerrePositivity.EInfinity.SimplicialLocalization
