module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.OverCanonicalCocone
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.NatTransHomotopyComponent
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpacePrismPoint
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeFamilyUnderlying
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceIntervalComparison

/-!
# 通常の余錐の全 prism と同じ自然変換の円柱

概要：通常の余錐の join 表示を区間へ展開し、元の自然変換を回収する。
方針：nerve の strict Segal 性と全一次単体での評価を使う。
規約：全パラメータを保ち、点ごとのホモトピー類の比較では代用しない。
使われ方：実屋根評価三角形の標準右脚との同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open CategoryTheory Limits Opposite SSet MonoidalCategory MonoidalClosed
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable {I C : Type u} [Category.{u} I] [Category.{u} C]

lemma nerveNatTransHomotopy_mixed {F G : I ⥤ C} (η : F ⟶ G) (a : (nerve I) _⦋1⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy η).h.app (op ⦋1⦌)
      (a, stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)) =
        ComposableArrows.mk₁ (F.map a.hom ≫ η.app (a.obj 1)) := by
  let t : (nerve (I × (I ⥤ C))) _⦋1⦌ := a.prod' (ComposableArrows.mk₁ η)
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso_uncurry I C) (op ⦋1⦌)) t
  change (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso I C).hom.app (op ⦋1⦌)
    (ComposableArrows.mk₁ η)).app (op ⦋1⦌) (𝟙 (op ⦋1⦌))) a = _ at h
  change (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso I C).hom.app (op ⦋1⦌)
    (ComposableArrows.mk₁ η)).app (op ⦋1⦌) (𝟙 (op ⦋1⦌))) a = _
  refine h.trans ?_
  refine ComposableArrows.ext₁ ?_ ?_ ?_
  · rfl
  · rfl
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

lemma rightMappingSpacePrism_mixed {K : SSet.{u}} (a : K _⦋1⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism K).app (op ⦋1⦌)
      (stdSimplex.objEquiv.symm (𝟙 ⦋1⦌), a) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.joinCoconeLegSimplex (K.δ 1 a) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap K Δ[0]).app (op ⦋1⦌)
    ((a, stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) 1) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_app]
  have hc : ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} 0 0).inv.app (op ⦋1⦌)
      (stdSimplex.objEquiv.symm (𝟙 ⦋1⦌))).1 = (1 : Fin 3) := by decide
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ hc
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap_congr K (congrArg Fin.val hc) rfl
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.prefixIncl 2 _ _) (SimplexCategory.δ (1 : Fin 2)).toOrderHom
      (by intro i j hij; fin_cases j; exact hij) a a rfl
  · apply stdSimplex.ext
    intro i
    apply Fin.ext
    omega

lemma nerveCoconePrism_eq_natTrans (F : I ⥤ C) (c : Cocone F) :
    (β_ (nerve I) (Δ[1] : SSet.{u})).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism (nerve I) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv c).val = (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy c.ι).h := by
  let L := (β_ (nerve I) (Δ[1] : SSet.{u})).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism (nerve I) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv c).val
  have h₀ : SSet.ι₀ ≫ L = nerveMap F := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (nerve I) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism (nerve I) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv c).val = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism_zero]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv c).property
  have h₁ : SSet.ι₁ ≫ L = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c.pt) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (nerve I) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism (nerve I) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv c).val = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism_one, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCocone_point]
    change SSet.const (stdSimplex.obj₀Equiv.symm 0) ≫
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c.pt) = _
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.const_point_comp_yoneda _
  apply _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerve_hom_ext_one
  rintro ⟨a, t⟩
  have ht : t = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) 1 ∨
      t = stdSimplex.objEquiv.symm (𝟙 ⦋1⦌) ∨
      t = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 1) 1 := by
    have hm : (t (0 : Fin 2)).val ≤ (t (1 : Fin 2)).val :=
      stdSimplex.monotone_apply t (show (0 : Fin 2) ≤ 1 by decide)
    by_cases h₁ : (t (1 : Fin 2)).val = 0
    · left
      apply stdSimplex.ext
      intro i
      fin_cases i
      · apply Fin.ext
        change (t (0 : Fin 2)).val = 0
        omega
      · apply Fin.ext
        change (t (1 : Fin 2)).val = 0
        exact h₁
    · by_cases h₀ : (t (0 : Fin 2)).val = 0
      · right; left
        apply stdSimplex.ext
        intro i
        fin_cases i
        · apply Fin.ext
          exact h₀
        · apply Fin.ext
          change (t (1 : Fin 2)).val = 1
          omega
      · right; right
        apply stdSimplex.ext
        intro i
        fin_cases i
        · apply Fin.ext
          change (t (0 : Fin 2)).val = 1
          omega
        · apply Fin.ext
          change (t (1 : Fin 2)).val = 1
          omega
  rcases ht with rfl | rfl | rfl
  · have h := ConcreteCategory.congr_hom (NatTrans.congr_app h₀ (op ⦋1⦌)) a
    have h' := ConcreteCategory.congr_hom
      (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy c.ι).h₀ (op ⦋1⦌)) a
    exact h.trans h'.symm
  · change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv c).val.app (op ⦋1⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism (nerve I)).app (op ⦋1⦌)
        (stdSimplex.objEquiv.symm (𝟙 ⦋1⦌), a)) = _
    rw [rightMappingSpacePrism_mixed]
    have ha : (nerve I).δ 1 a = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (a.obj 0) := ComposableArrows.ext₀ rfl
    rw [ha, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCocone_leg, nerveNatTransHomotopy_mixed]
    apply congrArg ComposableArrows.mk₁
    exact ((c.ι.naturality a.hom).trans (Category.comp_id _)).symm
  · have h := ConcreteCategory.congr_hom (NatTrans.congr_app h₁ (op ⦋1⦌)) a
    have h' := ConcreteCategory.congr_hom
      (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy c.ι).h₁ (op ⦋1⦌)) a
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveMap_const] at h'
    have ht₁ : ((SSet.ι₁ (X := nerve I)).app (op ⦋1⦌) a).2 =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 1) 1 := by
      apply stdSimplex.ext
      intro i
      fin_cases i <;> rfl
    change L.app (op ⦋1⦌) (a, _) = _
    rw [← ht₁]
    exact h.trans h'.symm

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
