module

public import SerrePositivity.InfinityCategories.F1B.KanLeftCanonicalHom
public import SerrePositivity.InfinityCategories.F1B.KanInitialBoundaryHomComparison
public import SerrePositivity.InfinityCategories.F1B.KanUniversalProperty
public import SerrePositivity.InfinityCategories.Stable.RelativeInitialVertices

/-!
概要：指定変換に両立する二つの左 Kan 拡張間の射の各点での可逆性。
方針：局所普遍余錐を比較し、制限の Hom 単射性で標準余錐間の射との可換性を示す。
規約：単に各点の値が同型であることから指定射の可逆性を推論しない。
使われ方：構成済みの普遍的な候補から任意の指定 Kan 変換への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：指定変換に両立する左 Kan 拡張間の比較射は各点で可逆。
方針：両方の普遍余錐の間に可逆な比較射を作り、標準余錐への輸送との可換性で頂点へ移す。
規約：K と C の quasicategory 性は不要。
使われ方：点ごとの Kan 条件から h Fun の大域的同型を得る主経路。 -/
lemma kanLeftComparison_component_isIso {K C D : SSet.{u}} [Quasicategory D]
    (δ : K ⟶ C) {F₀ : K ⟶ D} {F G : C ⟶ D}
    (β : SSet.Homotopy F₀ (δ ≫ F)) (γ : SSet.Homotopy F₀ (δ ≫ G))
    (hβ : IsLeftKanExtension δ F₀ F β) (hγ : IsLeftKanExtension δ F₀ G γ)
    (η : FunctorHom F G)
    (hη : leftKanHomMap δ (SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy β)) G η =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy γ))
    (c : C _⦋0⦌) : IsIso (functorHomEvaluate η c) := by
  obtain ⟨t, ht⟩ := hβ c
  obtain ⟨s, hs⟩ := hγ c
  let p := coconeRestriction (leftKanShape δ c) D
  let P := (hoFunctor.map p).toFunctor
  let e := SSet.Truncated.HomotopyCategory.homMk t.edge
  let f := SSet.Truncated.HomotopyCategory.homMk s.edge
  let a := kanLeftCanonicalHom δ c η
  let u : P.obj (HomotopyCategory.mk (functorVertex t.cocone.val)) ⟶
      P.obj (HomotopyCategory.mk (functorVertex s.cocone.val)) :=
    eqToHom (congrArg (fun q ↦ HomotopyCategory.mk (functorVertex q))
      (t.cocone.property.trans s.cocone.property.symm))
  have hl := congrArg
    (fun q ↦ (hoFunctor.map ((pre (leftKanProjection δ c)).app D)).toFunctor.map q) hη
  change (hoFunctor.map ((pre (leftKanProjection δ c)).app D)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β) ≫
        (hoFunctor.map ((pre δ).app D)).toFunctor.map η) = _ at hl
  rw [CategoryTheory.Functor.map_comp] at hl
  have hb : P.map e ≫ P.map a = u ≫ P.map f := by
    dsimp only [P, p, e, f, a, u]
    rw [kanLeftTransport_restriction_hom, kanLeftCanonicalHom_restriction,
      kanLeftTransport_restriction_hom]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    erw [reassoc_of% hl]
  obtain ⟨m, hm, _, hmcomm⟩ := exists_kanInitialBoundaryHom_comparison p
    (functorVertex t.cocone.val) (functorVertex s.cocone.val)
    (functorVertex (leftKanCanonicalCocone δ F c).val)
    (functorVertex (leftKanCanonicalCocone δ G c).val)
    ht.initialBoundaryLifting hs.initialBoundaryLifting e f a u
      (by dsimp only [u]; infer_instance) hb
  let V := (hoFunctor.map (coconeApexEvaluation (leftKanShape δ c) D)).toFunctor
  have : IsIso m := hm
  have : IsIso (V.map e) := kanLeftTransport_apex_isIso t
  have : IsIso (V.map f) := kanLeftTransport_apex_isIso s
  have hsq := congrArg V.map hmcomm
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at hsq
  have : IsIso (V.map e ≫ V.map a) := by
    rw [hsq]
    infer_instance
  have ha : IsIso (V.map a) := IsIso.of_isIso_comp_left (V.map e) (V.map a)
  exact kanLeftCanonicalHom_component_isIso δ c η ha

end SerrePositivity.InfinityCategories.F1B
