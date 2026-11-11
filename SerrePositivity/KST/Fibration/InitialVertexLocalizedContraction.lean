module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialTerminalWeakContractibility
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization

/-! # 始対象の元の収縮による一点への射の局所化可逆性 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 同じ実ホモトピー逆を anodyne 局所化へ写す。モデル構造の仮定は不要。 -/
theorem homotopyEquivalence_anodyneQ_isIso {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence f) :
    IsIso (AnodyneHomotopy.anodyneQ.map f) := by
  obtain ⟨g, ⟨H⟩, ⟨K⟩⟩ := hf
  let Q := AnodyneHomotopy.anodyneQ
  let e : Q.obj X ≅ Q.obj Y := {
    hom := Q.map f
    inv := Q.map g
    hom_inv_id := (Q.map_comp _ _).symm.trans
      ((AnodyneHomotopy.map_homotopy_eq Q SSet.anodyneExtensions.Q_inverts H).trans
        (Q.map_id _))
    inv_hom_id := (Q.map_comp _ _).symm.trans
      ((AnodyneHomotopy.map_homotopy_eq Q SSet.anodyneExtensions.Q_inverts K).trans
        (Q.map_id _)) }
  exact e.isIso_hom

/-- 元の始対象からの実収縮によって、同じ一点への射は局所化同型となる。 -/
theorem initialVertex_toPoint_localized_isIso {X : SSet.{u}} {x : X _⦋0⦌}
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x) :
    IsIso (AnodyneHomotopy.anodyneQ.map (terminal.from X)) :=
  homotopyEquivalence_anodyneQ_isIso _ hx.terminalFrom_isSimplicialHomotopyEquivalence

end SerrePositivity.KST.Fibration
