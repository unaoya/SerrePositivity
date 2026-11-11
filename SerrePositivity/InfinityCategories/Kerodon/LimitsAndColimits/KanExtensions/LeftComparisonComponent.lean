module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitRelativeBoundary

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeFamily
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeRestrictionCartesianEdge
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.InitialBoundaryHomComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Definition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCanonicalHom
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.UniversalProperty

/-!
概要：指定変換に両立する二つの左 Kan 拡張間の射の各点での可逆性。
方針：局所普遍余錐を比較し、制限の Hom 単射性で標準余錐間の射との可換性を示す。
規約：単に各点の値が同型であることから指定射の可逆性を推論しない。
使われ方：構成済みの普遍的な候補から任意の指定 Kan 変換への移送。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：指定変換に両立する左 Kan 拡張間の比較射は各点で可逆。
方針：両方の普遍余錐の間に可逆な比較射を作り、標準余錐への輸送との可換性で頂点へ移す。
規約：K と C の quasicategory 性は不要。
使われ方：点ごとの Kan 条件から h Fun の大域的同型を得る主経路。 -/
lemma kanLeftComparison_component_isIso {K C D : SSet.{u}} [Quasicategory D]
    (δ : K ⟶ C) {F₀ : K ⟶ D} {F G : C ⟶ D}
    (β : SSet.Homotopy F₀ (δ ≫ F)) (γ : SSet.Homotopy F₀ (δ ≫ G))
    (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension δ F₀ F β) (hγ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension δ F₀ G γ)
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G)
    (hη : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanHomMap δ (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β)) G η =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy γ))
    (c : C _⦋0⦌) : IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate η c) := by
  obtain ⟨t, ht⟩ := hβ c
  obtain ⟨s, hs⟩ := hγ c
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c) D
  let P := (hoFunctor.map p).toFunctor
  let e := SSet.Truncated.HomotopyCategory.homMk t.edge
  let f := SSet.Truncated.HomotopyCategory.homMk s.edge
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonicalHom δ c η
  let u : P.obj (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex t.cocone.val)) ⟶
      P.obj (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s.cocone.val)) :=
    eqToHom (congrArg (fun q ↦ HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex q))
      (t.cocone.property.trans s.cocone.property.symm))
  have hl := congrArg
    (fun q ↦ (hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ c)).app D)).toFunctor.map q) hη
  change (hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ c)).app D)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β) ≫
        (hoFunctor.map ((pre δ).app D)).toFunctor.map η) = _ at hl
  rw [CategoryTheory.Functor.map_comp] at hl
  have hb : P.map e ≫ P.map a = u ≫ P.map f := by
    dsimp only [P, p, e, f, a, u]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftTransport_restriction_hom, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonicalHom_restriction,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftTransport_restriction_hom]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    erw [reassoc_of% hl]
  obtain ⟨m, hm, _, hmcomm⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.exists_kanInitialBoundaryHom_comparison p
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex t.cocone.val) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s.cocone.val)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ F c).val)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ G c).val)
    ht.initialBoundaryLifting hs.initialBoundaryLifting e f a u
      (by dsimp only [u]; infer_instance) hb
  let V := (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeApexEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c) D)).toFunctor
  have : IsIso m := hm
  have : IsIso (V.map e) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftTransport_apex_isIso t
  have : IsIso (V.map f) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftTransport_apex_isIso s
  have hsq := congrArg V.map hmcomm
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at hsq
  have : IsIso (V.map e ≫ V.map a) := by
    rw [hsq]
    infer_instance
  have ha : IsIso (V.map a) := IsIso.of_isIso_comp_left (V.map e) (V.map a)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonicalHom_component_isIso δ c η ha

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
