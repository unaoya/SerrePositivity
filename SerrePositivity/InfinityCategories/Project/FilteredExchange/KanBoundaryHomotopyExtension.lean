module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanFibrationRelativeHomotopyLift

/-!
概要：指定境界の全ホモトピーを、Kan 標的への全体射のホモトピーへ延長する。
方針：終対象への Kan fibration に沿う相対ホモトピー持ち上げ。
規約：境界の全円柱を厳密に保持。使われ方：元の境界値への輸送に合わせた標的射の補正。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：境界の指定円柱を全体へ延長し、終点の境界値も厳密に保持する。
方針：終対象への相対持ち上げ。規約：有限性不要。使われ方：標的射の境界を元の値に揃える。 -/
lemma kanComplex_extend_boundary_homotopy {A K X : SSet.{u}} [KanComplex X]
    (i : A ⟶ K) [Mono i] (f : K ⟶ X) (a : A ⟶ X)
    (L : SSet.Homotopy (i ≫ f) a) :
    ∃ g : K ⟶ X, i ≫ g = a ∧ ∃ G : SSet.Homotopy f g,
      (i ▷ (Δ[1] : SSet.{u})) ≫ G.h = L.h := by
  let H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl f) (terminal.from X)
  have hL : L.h ≫ terminal.from X = (i ▷ (Δ[1] : SSet.{u})) ≫ H.h :=
    terminalIsTerminal.hom_ext _ _
  obtain ⟨g, hg, G, hG, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanFibration_lift_homotopy_relative
    (terminal.from X) i f H a L hL
  exact ⟨g, hg, G, hG⟩

end SerrePositivity.InfinityCategories.Project.FilteredExchange
