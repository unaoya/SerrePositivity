module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.ComposableHomotopyHorn

/-!
概要：quasicategory 内の二円柱を、元の二辺を保持する三角形へ延長する。
方針：二次内ホーンのパラメータ積の inner anodyne 性。
規約：標的に Kan 性を要求しない。使われ方：元の全空間内の境界輸送の合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：元の二円柱を二辺として厳密に保持する三角形が存在する。
方針：パラメータ付き内ホーンを充填。規約：quasicategory のみ。使われ方：境界輸送の合成。 -/
lemma exists_quasiHomotopyTriangle {A X : SSet.{u}} [Quasicategory X]
    {f₀ f₁ f₂ : A ⟶ X} (U : SSet.Homotopy f₀ f₁) (V : SSet.Homotopy f₁ f₂) :
    ∃ F : (Δ[2] : SSet.{u}) ⊗ A ⟶ X,
      ((horn 2 1).ι ▷ A) ≫ F = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.composableHomotopyHorn U V := by
  have hi := (innerAnodyneExtensions.horn_ι
    (by decide : 0 < (1 : Fin 3)) (by decide : (1 : Fin 3) < Fin.last 2)).whiskerRight A
  have := hi (terminal.from X) (mem_innerFibrations _)
  have sq : CommSq (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.composableHomotopyHorn U V) ((horn 2 1).ι ▷ A)
      (terminal.from X) (terminal.from ((Δ[2] : SSet.{u}) ⊗ A)) :=
    ⟨terminalIsTerminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

end SerrePositivity.InfinityCategories.Project.FilteredExchange
