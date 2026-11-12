module
public import SerrePositivity.KST.SConstruction.CoherentHomotopyComponentCalculus

/-! # 全入力円柱の各単体への整合的な制限
概要：同じ円柱を入力の全単体へ制限し、端点・頂点・面と退化の厳密な式を与える。
方針：Yoneda の単体表示を円柱に前合成し、その自然性を使う。
規約：quasicategory 性は不要。各射の square を独立に選び直さない。
使われ方：固定構造射を四辺に持つ自然性 square と全合成列の整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 全入力円柱を指定した入力単体へ制限した、同じ円柱の prism。 -/
def homotopySimplexPrism {A X : SSet.{u}} {F G : A ⟶ X}
    (H : SSet.Homotopy F G) {n : ℕ} (s : A _⦋n⦌) :
    (Δ[n] : SSet.{u}) ⊗ Δ[1] ⟶ X :=
  (SSet.yonedaEquiv.symm s ▷ (Δ[1] : SSet.{u})) ≫ H.h

/-- prism の時刻零は、元の始域図式の同じ単体。 -/
lemma homotopySimplexPrism_zero {A X : SSet.{u}} {F G : A ⟶ X}
    (H : SSet.Homotopy F G) {n : ℕ} (s : A _⦋n⦌) :
    SSet.ι₀ ≫ homotopySimplexPrism H s = SSet.yonedaEquiv.symm s ≫ F :=
  (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H (SSet.yonedaEquiv.symm s)).h₀

/-- prism の時刻一は、元の終域図式の同じ単体。 -/
lemma homotopySimplexPrism_one {A X : SSet.{u}} {F G : A ⟶ X}
    (H : SSet.Homotopy F G) {n : ℕ} (s : A _⦋n⦌) :
    SSet.ι₁ ≫ homotopySimplexPrism H s = SSet.yonedaEquiv.symm s ≫ G :=
  (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H (SSet.yonedaEquiv.symm s)).h₁

/-- 入力の全単体作用による制限は、同じ全体円柱の制限として厳密に可換。 -/
lemma homotopySimplexPrism_naturality {A X : SSet.{u}} {F G : A ⟶ X}
    (H : SSet.Homotopy F G) {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (s : A _⦋n⦌) :
    (SSet.stdSimplex.map θ ▷ (Δ[1] : SSet.{u})) ≫ homotopySimplexPrism H s =
      homotopySimplexPrism H (A.map θ.op s) := by
  unfold homotopySimplexPrism
  rw [← comp_whiskerRight_assoc, SSet.yonedaEquiv_symm_naturality_left]

/-- 全体円柱を頂点で制限すると、同じ成分の辺の Yoneda 表示を厳密に回収する。 -/
lemma homotopy_vertex_restriction {A X : SSet.{u}} {F G : A ⟶ X}
    (H : SSet.Homotopy F G) (a : A _⦋0⦌) :
    lift (SSet.const a) (𝟙 (Δ[1] : SSet.{u})) ≫ H.h =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H a).edge := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex]
  exact ((SSet.yonedaEquiv.symm_apply_eq).mpr (homotopyVertexEdge_yoneda H a).symm).symm

/-- prism の任意の入力頂点の縦辺は、元の同じ成分の辺そのもの。 -/
lemma homotopySimplexPrism_vertex {A X : SSet.{u}} {F G : A ⟶ X}
    (H : SSet.Homotopy F G) {n : ℕ} (s : A _⦋n⦌)
    (a : (Δ[n] : SSet.{u}) _⦋0⦌) :
    lift (SSet.const a) (𝟙 (Δ[1] : SSet.{u})) ≫ homotopySimplexPrism H s =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H
        ((SSet.yonedaEquiv.symm s).app (Opposite.op ⦋0⦌) a)).edge := by
  unfold homotopySimplexPrism
  rw [lift_whiskerRight_assoc, SSet.const_comp]
  exact homotopy_vertex_restriction H _

end SerrePositivity.KST.SConstruction
