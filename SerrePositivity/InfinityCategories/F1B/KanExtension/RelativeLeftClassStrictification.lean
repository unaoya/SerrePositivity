module

public import SerrePositivity.InfinityCategories.F1B.KanComplex.HomotopyRepresentativeLift
public import SerrePositivity.InfinityCategories.F1B.KanComplex.HomotopyOfEq
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeLeftStrictification
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeLeftHomotopyInvariant

/-!
概要：底での類が恒等な指定相対左 Kan 単位を元と標的を固定して厳密化する。
方針：同じ類を保って像の円柱を定値に直し、既存の底固定の path 延長へ渡す。
規約：単位の代表が最初から底で定値であることを要求しない。
使われ方：一般の isofibration 上の相対左 Kan 制限の厳密な存在。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：像の類が等式の恒等射なら相対左 Kan 関手を元と標的を保って厳密化できる。
方針：元の単位の類を保って底の代表を定値に修正し、その代表で相対厳密化する。
規約：hFU は底での制限の等式であり、h は指定単位の像の類についての条件。
使われ方：元の関手圏での一般の相対左 Kan 延長の頂点の持ち上げ。 -/
lemma exists_kanRelativeLeftCanonical_strictification_of_image_class
    {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) (hU : SerrePositivity.InfinityCategories.F1B.EquivalenceLifting U)
    (δ : K ⟶ C) [Mono δ] [InnerFibration δ] (hδ : IsFullyFaithful δ)
    {F₀ : K ⟶ D} {F : C ⟶ D} (β : SSet.Homotopy F₀ (δ ≫ F))
    (hβ : IsRelativeLeftKanExtension U δ F₀ F β)
    (hFU : F₀ ≫ U = (δ ≫ F) ≫ U)
    (h : SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (functorHomotopyPostcomp β U)) =
      eqToHom (congrArg (fun q : K ⟶ E ↦ HomotopyCategory.mk (functorVertex q)) hFU)) :
    ∃ G : C ⟶ D, δ ≫ G = F₀ ∧ G ≫ U = F ≫ U ∧
      IsRelativeLeftKanExtendedFrom U δ G := by
  have : InnerFibration U := hU.innerFibration
  have hh : SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (functorHomotopyPostcomp β U)) =
      SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (kanHomotopyOfEq hFU)) := by
    rw [kanHomotopyOfEq_hom]
    exact h
  obtain ⟨β', hβ'U, hc⟩ := exists_kanHomotopyRepresentative_lift U β (kanHomotopyOfEq hFU) hh
  have hβ' := (kanIsRelativeLeftKanExtension_iff_of_homMk_eq U δ F₀ F β' β hc).2 hβ
  apply exists_kanRelativeLeftCanonical_strictification_of_unit_over_identity U hU δ hδ β' hβ'
  simpa only [kanHomotopyOfEq, functorHomotopyRefl, Category.assoc] using hβ'U

end SerrePositivity.InfinityCategories.F1B
