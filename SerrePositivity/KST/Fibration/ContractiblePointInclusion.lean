module
public import SerrePositivity.KST.Fibration.InitialVertexLocalizedContraction
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-! # 可縮な対象への指定した零次標準単体の包含の可逆性 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 同じ一点への射が局所化同型なら、指定した任意の零次単体の包含も局所化同型。 -/
theorem pointInclusion_localized_isIso {Y : SSet.{u}} (z : Δ[0] ⟶ Y)
    (hy : IsIso (AnodyneHomotopy.anodyneQ.map (terminal.from Y))) :
    IsIso (AnodyneHomotopy.anodyneQ.map z) := by
  let e : (Δ[0] : SSet.{u}) ≅ ⊤_ SSet.{u} :=
    stdSimplex.isTerminalObj₀.uniqueUpToIso (terminalIsTerminal)
  have he : z ≫ terminal.from Y = e.hom := terminal.hom_ext _ _
  have hc : IsIso (AnodyneHomotopy.anodyneQ.map z ≫
      AnodyneHomotopy.anodyneQ.map (terminal.from Y)) := by
    rw [← Functor.map_comp, he]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp hc

end SerrePositivity.KST.Fibration
