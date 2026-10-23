module

public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftPath
public import SerrePositivity.InfinityCategories.Core.HomotopyBoundaryExtension
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic

/-!
概要：Kan fibration に沿って指定した全ホモトピーを始点固定で持ち上げる。
方針：全ホーンの右持ち上げ性を left fibration の prism 持ち上げへ渡す。
規約：底の全円柱を厳密に保持する。
使われ方：Kan 引き戻し内で二入力を元の全空間の射へ変形する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：Kan fibration は left fibration の全ホーンを持ち上げる。
方針：全ホーンの右持ち上げ性を制限する。
規約：具体的な単体集合の充填性。使われ方：任意の部分円柱を保つ持ち上げ。 -/
lemma kanFibration_leftFibration {E B : SSet.{u}} (p : E ⟶ B) [Fibration p] :
    LeftFibration p := ⟨by
  intro A B i hi
  cases hi with
  | intro j hj =>
    exact (anodyneExtensions.horn_ι j) p ((HomotopicalAlgebra.fibration_iff p).mp inferInstance)⟩

/-- 概要：Kan fibration は任意のパラメータの指定円柱を始点固定で持ち上げる。
方針：ホーンの持ち上げから left fibration の prism 持ち上げを使う。
規約：全円柱の底が厳密に一致。使われ方：path の指定両端の同時変形。 -/
lemma kanFibration_lift_homotopy {K E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    (f : K ⟶ E) {b : K ⟶ B} (H : SSet.Homotopy (f ≫ p) b) :
    ∃ g : K ⟶ E, ∃ G : SSet.Homotopy f g, G.h ≫ p = H.h := by
  have := kanFibration_leftFibration p
  let a := (β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h
  have ha : f ≫ p = prismEndpoint 0 K ≫ a := by
    change f ≫ p = SSet.ι₀ ≫ H.h
    exact H.h₀.symm
  obtain ⟨L, hL₀, hLp⟩ := leftFibration_lift_prism p f a ha
  let R := (β_ K (Δ[1] : SSet.{u})).hom ≫ L
  refine ⟨SSet.ι₁ ≫ R, ⟨R, ?_, rfl, ?_⟩, ?_⟩
  · change prismEndpoint 0 K ≫ L = f
    exact hL₀
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property
  · dsimp only [R]
    rw [Category.assoc, hLp]
    dsimp only [a]
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

end SerrePositivity.InfinityCategories.F2
