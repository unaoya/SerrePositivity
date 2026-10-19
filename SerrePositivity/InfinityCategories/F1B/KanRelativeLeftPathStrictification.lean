module

public import SerrePositivity.InfinityCategories.F1B.KanRelativeEquivalencePathExtension
public import SerrePositivity.InfinityCategories.F1B.KanRelativeLeftUnitCanonical

/-!
概要：底で定値な指定可逆 path から元と標的を保つ相対左 Kan 厳密化を得る。
方針：終点を固定して path を延長し、その始点へ標準局所条件を同型で移す。
規約：U の像は元の関手の像と厳密に一致する。
使われ方：相対左 Kan 制限の頂点の持ち上げで必要な厳密な図式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：底で定値な部分図式上の可逆 path を使って相対左 Kan 関手を厳密化する。
方針：部分 path・終点 F・底の定値 path を同時に延長し、始点の標準条件を回収する。
規約：元の図式 F₀ と底の図式 F≫U の両方を射の等式として保つ。
使われ方：元の全部分圏からの相対制限での厳密な頂点の持ち上げ。 -/
lemma exists_kanRelativeLeftCanonical_strictification_of_path {K C D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) (hU : KanEquivalenceLifting U)
    (δ : K ⟶ C) [Mono δ] {F₀ : K ⟶ D} {F : C ⟶ D}
    (hF : IsRelativeLeftKanExtendedFrom U δ F) (a : K ⟶ equivalencePath D)
    (h₀ : a ≫ equivalencePathEndpoint D 0 = F₀)
    (h₁ : a ≫ equivalencePathEndpoint D 1 = δ ≫ F)
    (ha : a ≫ equivalencePathMap U = δ ≫ (F ≫ U ≫ equivalencePathRefl E)) :
    ∃ G : C ⟶ D, δ ≫ G = F₀ ∧ G ≫ U = F ≫ U ∧
      IsRelativeLeftKanExtendedFrom U δ G := by
  have : InnerFibration U := hU.innerFibration
  obtain ⟨L, hLδ, hLU, hL₁⟩ := exists_kanRelativeEquivalencePath_extension U hU δ a
    (F ≫ U ≫ equivalencePathRefl E) F ha h₁
    (by simp only [Category.assoc, equivalencePathRefl_endpoint, Category.comp_id])
  let G := L ≫ equivalencePathEndpoint D 0
  have e : FunctorIso G F := by
    have e := kanEquivalencePath_functorIso L
    rw [hL₁] at e
    exact e
  refine ⟨G, ?_, ?_, kanIsRelativeLeftKanExtendedFrom_of_functorIso U δ e.symm hF⟩
  · change δ ≫ L ≫ equivalencePathEndpoint D 0 = F₀
    rw [← Category.assoc, hLδ, h₀]
  · change (L ≫ equivalencePathEndpoint D 0) ≫ U = F ≫ U
    rw [Category.assoc, ← equivalencePathMap_endpoint, ← Category.assoc, hLU]
    simp only [Category.assoc, equivalencePathRefl_endpoint, Category.comp_id]

end SerrePositivity.InfinityCategories.F1B
