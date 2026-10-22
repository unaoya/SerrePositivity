module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessSquare

/-!
概要：全経路の射が同じ証人へ、相対二重経路を端点・底と共に移す。
方針：外側の経路評価から端点と底の等式を導き、全二重経路を保持する。
規約：経路の一致は明示入力。使われ方：因子分解比較の端点正規化。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitnessSquare
variable {R : Type u} [CommRing R] {B W : Mon (Complex R)} {N : Bimod B B}
  {q q' : W ⟶ B} {a b a' b' : W ⟶ algebra B N}
  {v w : RelativeWitness q N a b} (h : RelativeWitnessSquare v w)
  (v' w' : RelativeWitness q' N a' b') (hv : v.hom = v'.hom) (hw : w.hom = w'.hom)

include v v' hv in
lemma reindex_source : a = a' :=
  v.source_eq.symm.trans ((congrArg (fun k => k ≫ DGAlgebra.Path.source R (algebra B N)) hv).trans
    v'.source_eq)

include v v' hv in
lemma reindex_target : b = b' :=
  v.target_eq.symm.trans ((congrArg (fun k => k ≫ DGAlgebra.Path.target R (algebra B N)) hv).trans
    v'.target_eq)

include v v' hv in
lemma reindex_base : q = q' :=
  v.source_projection.symm.trans
    ((congrArg (fun k => k ≫ projection B N) (reindex_source v' hv)).trans v'.source_projection)

/-- 同じ二つの全経路を異なる等式証明で表示しても、実二重経路を選び直さない。 -/
def reindex : RelativeWitnessSquare v' w' where
  hom := h.hom
  source_eq := h.source_eq.trans hv
  target_eq := h.target_eq.trans hw
  source_trace := h.source_trace.trans (congrArg
    (fun k => k ≫ DGAlgebra.Path.diagonal R (algebra B N)) (reindex_source v' hv))
  target_trace := h.target_trace.trans (congrArg
    (fun k => k ≫ DGAlgebra.Path.diagonal R (algebra B N)) (reindex_target v' hv))
  projection_eq := h.projection_eq.trans (congrArg (fun k =>
    (k ≫ DGAlgebra.Path.diagonal R B) ≫
      DGAlgebra.Path.diagonal R (DGAlgebra.Path.algebra R B)) (reindex_base v' hv))

end SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitnessSquare
