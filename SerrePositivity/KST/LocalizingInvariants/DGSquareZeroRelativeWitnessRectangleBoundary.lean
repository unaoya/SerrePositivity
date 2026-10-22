module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessRectangle

/-!
概要：輪郭補正の外側両端と内側両辺を、元の四辺に同定する。
方針：実 affine 式を四評価へ後合成し、connection の四辺の式で相殺する。
規約：底と全経路を保つ。使われ方：固定端点の class 二重経路の充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Preadditive
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitnessRectangle
variable {R : Type u} [CommRing R] {B W : Mon (Complex R)} {N : Bimod B B}
  {q : W ⟶ B} {a₀ a₁ b₀ b₁ : W ⟶ algebra B N}
  {v : RelativeWitness q N a₀ b₀} {w : RelativeWitness q N a₁ b₁}
  {l : RelativeWitness q N a₀ a₁} {r : RelativeWitness q N b₀ b₁}
  (s : RelativeWitnessRectangle v w l r)

lemma contourHom_source : s.contourHom ≫
    DGAlgebra.Path.source R (DGAlgebra.Path.algebra R (algebra B N)) = (v.comp r).hom := by
  apply Mon.Hom.ext
  have h := congrArg (fun k => k ≫ (DGAlgebra.Path.source R
    (DGAlgebra.Path.algebra R (algebra B N))).hom) s.contourHom_linear
  simp only [add_comp, sub_comp, ← Mon.comp_hom', Category.assoc,
    DGAlgebra.Path.connection_source, DGAlgebra.Path.diagonal_source,
    DGAlgebra.Path.map_source, Category.comp_id, s.source_eq,
    reassoc_of% r.source_eq, reassoc_of% l.source_eq] at h
  rw [RelativeWitness.comp_hom_linear]
  exact h.trans (by abel)

lemma contourHom_target : s.contourHom ≫
    DGAlgebra.Path.target R (DGAlgebra.Path.algebra R (algebra B N)) = (l.comp w).hom := by
  apply Mon.Hom.ext
  have h := congrArg (fun k => k ≫ (DGAlgebra.Path.target R
    (DGAlgebra.Path.algebra R (algebra B N))).hom) s.contourHom_linear
  simp only [add_comp, sub_comp, ← Mon.comp_hom', Category.assoc,
    DGAlgebra.Path.connection_target, DGAlgebra.Path.diagonal_target,
    DGAlgebra.Path.map_target, Category.comp_id, s.target_eq,
    reassoc_of% l.target_eq] at h
  rw [RelativeWitness.comp_hom_linear]
  exact h.trans (by abel)

lemma contourHom_source_trace : s.contourHom ≫
    DGAlgebra.Path.map R (DGAlgebra.Path.source R (algebra B N)) =
      a₀ ≫ DGAlgebra.Path.diagonal R (algebra B N) := by
  apply Mon.Hom.ext
  have h := congrArg (fun k => k ≫ (DGAlgebra.Path.map R
    (DGAlgebra.Path.source R (algebra B N))).hom) s.contourHom_linear
  simp only [add_comp, sub_comp, ← Mon.comp_hom', Category.assoc,
    DGAlgebra.Path.connection_innerSource, DGAlgebra.Path.diagonal_naturality,
    ← DGAlgebra.Path.map_comp, DGAlgebra.Path.diagonal_source,
    DGAlgebra.Path.map_id, Category.comp_id, s.source_trace,
    reassoc_of% r.source_eq, reassoc_of% l.source_eq] at h
  exact h.trans (by abel)

lemma contourHom_target_trace : s.contourHom ≫
    DGAlgebra.Path.map R (DGAlgebra.Path.target R (algebra B N)) =
      b₁ ≫ DGAlgebra.Path.diagonal R (algebra B N) := by
  apply Mon.Hom.ext
  have h := congrArg (fun k => k ≫ (DGAlgebra.Path.map R
    (DGAlgebra.Path.target R (algebra B N))).hom) s.contourHom_linear
  simp only [add_comp, sub_comp, ← Mon.comp_hom', Category.assoc,
    DGAlgebra.Path.connection_innerTarget, DGAlgebra.Path.diagonal_naturality,
    ← DGAlgebra.Path.map_comp, DGAlgebra.Path.diagonal_target,
    DGAlgebra.Path.map_id, Category.comp_id, s.target_trace,
    reassoc_of% r.target_eq] at h
  exact h.trans (by abel)

/-- 動く四辺から、輪郭二経路の固定端点二重経路を実際に構成する。 -/
def contourSquare : RelativeWitnessSquare (v.comp r) (l.comp w) where
  hom := s.contourHom
  source_eq := s.contourHom_source
  target_eq := s.contourHom_target
  source_trace := s.contourHom_source_trace
  target_trace := s.contourHom_target_trace
  projection_eq := s.contourHom_projection

end SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitnessRectangle
