module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LeftFibrationPrismLift
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiniteShapes
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap

/-! # Left fibration の頂点 fiber の区間輸送

概要：底の辺に沿って fiber 全体を送り、その包含を結ぶ実際の区間族を得る。
方針：定値の底の辺の族を fiber 包含から持ち上げ、終端を標的の fiber へ戻す。
規約：輸送は選択を含み、辺の全体への像を厳密に保つ。使われ方：余錐の終点の変化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：底の辺の定値パラメーター族は時刻零で始点への定値射。
方針：区間の先頭包含を点の始点包含として読み、辺の始点の式を使う。
規約：パラメーター A は任意。使われ方：fiber 輸送の持ち上げの初期条件。 -/
lemma stablePrism_edge_zero {A B : SSet.{u}} {x y : B _⦋0⦌}
    (a : SSet.Truncated.Edge (X := (truncation 2).obj B) x y) :
    SSet.ι₀ ≫ snd A (Δ[1] : SSet.{u}) ≫ SSet.yonedaEquiv.symm a.edge = SSet.const x := by
  have hi : SSet.ι₀ ≫ snd A (Δ[1] : SSet.{u}) =
      stdSimplex.isTerminalObj₀.from A ≫ stdSimplex.δ (1 : Fin 2) := rfl
  rw [← Category.assoc, hi, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSimplex_source,
    SSet.yonedaEquiv_symm_zero, SSet.comp_const]

/-- 概要：底の辺の定値パラメーター族は時刻一で終点への定値射。
方針：区間の終端包含を点の終点包含として読み、辺の終点の式を使う。
規約：パラメーター A は任意。使われ方：fiber 輸送の終端の固定条件。 -/
lemma stablePrism_edge_one {A B : SSet.{u}} {x y : B _⦋0⦌}
    (a : SSet.Truncated.Edge (X := (truncation 2).obj B) x y) :
    SSet.ι₁ ≫ snd A (Δ[1] : SSet.{u}) ≫ SSet.yonedaEquiv.symm a.edge = SSet.const y := by
  have hi : SSet.ι₁ ≫ snd A (Δ[1] : SSet.{u}) =
      stdSimplex.isTerminalObj₀.from A ≫ stdSimplex.δ (0 : Fin 2) := rfl
  rw [← Category.assoc, hi, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSimplex_target,
    SSet.yonedaEquiv_symm_zero, SSet.comp_const]

/-- 概要：底の辺に沿う fiber の射と、それを包含後に実現する区間族のデータ。
方針：両端と底への像を射の等号で保持する。
規約：データの型自体には fibration 性を仮定しない。使われ方：二枝の輸送を同時に選ぶ。 -/
structure LeftFibrationFiberTransport {E B : SSet.{u}} (p : E ⟶ B)
    {x y : B _⦋0⦌} (a : SSet.Truncated.Edge (X := (truncation 2).obj B) x y) where
  map : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p x ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p y
  h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p x ⊗ (Δ[1] : SSet.{u}) ⟶ E
  h₀ : SSet.ι₀ ≫ h = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p x
  h₁ : SSet.ι₁ ≫ h = map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p y
  over : h ≫ p = snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p x) (Δ[1] : SSet.{u}) ≫ SSet.yonedaEquiv.symm a.edge

/-- 概要：任意の left fibration と底の辺に対して fiber 全体の輸送が存在する。
方針：始点の fiber 包含から定値の底の辺の族を持ち上げ、終端を終点の fiber に入れる。
規約：全空間と底の quasicategory 性は不要。使われ方：共通始点の余錐空間の輸送を先に選ぶ。 -/
lemma nonempty_leftFibrationFiberTransport {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    {x y : B _⦋0⦌} (a : SSet.Truncated.Edge (X := (truncation 2).obj B) x y) :
    Nonempty (LeftFibrationFiberTransport p a) := by
  obtain ⟨R, hR₀, hRp⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.leftFibration_prism_lift p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p x)
    (snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p x) (Δ[1] : SSet.{u}) ≫ SSet.yonedaEquiv.symm a.edge) (by
      rw [stablePrism_edge_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp])
  have hT : (SSet.ι₁ ≫ R) ≫ p = SSet.const y := by
    rw [Category.assoc, hRp, stablePrism_edge_one]
  refine ⟨{ map := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p y (SSet.ι₁ ≫ R) hT
            h := R
            h₀ := hR₀
            h₁ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι p y (SSet.ι₁ ≫ R) hT).symm
            over := hRp }⟩

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
