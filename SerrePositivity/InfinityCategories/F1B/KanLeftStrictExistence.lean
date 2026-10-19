module

public import SerrePositivity.InfinityCategories.F1B.KanLeftUnitCanonical
public import SerrePositivity.InfinityCategories.F1B.KanFunctorIsoExtension

/-!
概要：全部分圏包含に沿って元の図式を厳密に延長する左 Kan 関手を構成する。
方針：指定単位の逆同型を単射上で延長し、全体の同型で標準局所余極限性を移す。
規約：制限は自然同型でなく射の等式として元の図式に等しい。
使われ方：元の左 Kan 関手の全部分圏の制限の頂点全射性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：充満忠実な inner 単射上の左 Kan 拡張を元の図式へ厳密化できる。
方針：単位の逆同型を全体へ延長し、標準局所余錐の余極限性を同型で輸送する。
規約：元の図式 F₀ を厳密に保つ G を返す。
使われ方：元の左 Kan 関手の制限の頂点の持ち上げ。 -/
lemma exists_kanLeftCanonical_strictification {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D]
    (δ : K ⟶ C) [Mono δ] [InnerFibration δ] (hδ : IsFullyFaithful δ)
    {F₀ : K ⟶ D} {F : C ⟶ D} (β : SSet.Homotopy F₀ (δ ≫ F))
    (hβ : IsLeftKanExtension δ F₀ F β) :
    ∃ G : C ⟶ D, δ ≫ G = F₀ ∧
      ∀ c : C _⦋0⦌, IsColimitCone (leftKanCanonicalCocone δ G c) := by
  have hi := kanLeftKanExtension_unit_isIso δ hδ β hβ
  let e : FunctorIso (δ ≫ F) F₀ :=
    (asIso (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β))).symm
  obtain ⟨s⟩ := kanFunctorIsoExtension_nonempty δ F F₀ e
  have hF := kanLeftKanExtension_canonicalColimits_of_unit_isIso δ β hβ hi
  exact ⟨s.diagram, s.restriction, kanLeftCanonicalColimits_of_functorIso δ s.globalIso hF⟩

/-- 概要：各点の局所余極限があれば、包含上で元の図式に厳密に等しい左 Kan 関手が存在する。
方針：指定単位つきの大域的存在を使い、その単位の可逆性で厳密化する。
規約：δ は単射・inner・写像空間で充満忠実。通常の全部分複体の包含に適用できる。
使われ方：余極限から coherent に選ぶ元の関手圏の制限射の全射性。 -/
lemma exists_kanLeftCanonical_strict_extension_of_local_colimits {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D]
    (δ : K ⟶ C) [Mono δ] [InnerFibration δ] (hδ : IsFullyFaithful δ) (F₀ : K ⟶ D)
    (hcol : ∀ c : C _⦋0⦌, HasColimit (leftKanDiagram δ F₀ c)) :
    ∃ G : C ⟶ D, δ ≫ G = F₀ ∧
      ∀ c : C _⦋0⦌, IsColimitCone (leftKanCanonicalCocone δ G c) := by
  obtain ⟨F, β, hβ⟩ := exists_kanLeftExtension_of_local_colimits δ F₀ hcol
  exact exists_kanLeftCanonical_strictification δ hδ β hβ

end SerrePositivity.InfinityCategories.F1B
