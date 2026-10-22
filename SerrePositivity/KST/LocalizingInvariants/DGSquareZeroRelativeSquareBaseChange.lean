module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquareBaseChangeLift

/-!
概要：底変更した class 二重経路の内部両端を固定し、相対二重証人へ束ねる。
方針：経路の底射影と元の class 射への射影による一意性を使う。
規約：端点だけでなく全二重経路の射影を保持。使われ方：共通底での輸送比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable {R : Type u} [CommRing R] {A B W : Mon (Complex R)} (q : A ⟶ B) (N : Bimod B B)
  (a : W ⟶ A) {u v : W ⟶ algebra B N} {s t : RelativeWitness (a ≫ q) N u v}
  (h : RelativeWitnessSquare s t)

lemma baseChangeSquareHom_source_trace : baseChangeSquareHom q N a h ≫
    DGAlgebra.Path.map R (DGAlgebra.Path.source R (algebra A (bimoduleRestrict q N))) =
      baseChangeLift q N a u s.source_projection ≫
        DGAlgebra.Path.diagonal R (algebra A (bimoduleRestrict q N)) := by
  apply baseChangePath_hom_ext q N
  · rw [Category.assoc, ← DGAlgebra.Path.map_comp, ← DGAlgebra.Path.map_source,
      DGAlgebra.Path.map_comp, ← Category.assoc, baseChangeSquareHom_projection]
    simp only [Category.assoc, DGAlgebra.Path.diagonal_naturality]
    rw [← Category.assoc (DGAlgebra.Path.diagonal R A),
      DGAlgebra.Path.diagonal_source, Category.id_comp]
    rw [← Category.assoc, baseChangeLift_projection]
  · rw [Category.assoc, ← DGAlgebra.Path.map_comp, ← DGAlgebra.Path.map_source,
      DGAlgebra.Path.map_comp, ← Category.assoc, baseChangeSquareHom_map, h.source_trace]
    rw [Category.assoc, DGAlgebra.Path.diagonal_naturality,
      ← Category.assoc, baseChangeLift_map]

lemma baseChangeSquareHom_target_trace : baseChangeSquareHom q N a h ≫
    DGAlgebra.Path.map R (DGAlgebra.Path.target R (algebra A (bimoduleRestrict q N))) =
      baseChangeLift q N a v s.target_projection ≫
        DGAlgebra.Path.diagonal R (algebra A (bimoduleRestrict q N)) := by
  apply baseChangePath_hom_ext q N
  · rw [Category.assoc, ← DGAlgebra.Path.map_comp, ← DGAlgebra.Path.map_target,
      DGAlgebra.Path.map_comp, ← Category.assoc, baseChangeSquareHom_projection]
    simp only [Category.assoc, DGAlgebra.Path.diagonal_naturality]
    rw [← Category.assoc (DGAlgebra.Path.diagonal R A),
      DGAlgebra.Path.diagonal_target, Category.id_comp]
    rw [← Category.assoc, baseChangeLift_projection]
  · rw [Category.assoc, ← DGAlgebra.Path.map_comp, ← DGAlgebra.Path.map_target,
      DGAlgebra.Path.map_comp, ← Category.assoc, baseChangeSquareHom_map, h.target_trace]
    rw [Category.assoc, DGAlgebra.Path.diagonal_naturality,
      ← Category.assoc, baseChangeLift_map]

def baseChangeRelativeWitnessSquare : RelativeWitnessSquare
    (baseChangeRelativeWitness q N a s) (baseChangeRelativeWitness q N a t) where
  hom := baseChangeSquareHom q N a h
  source_eq := baseChangeSquareHom_source q N a h
  target_eq := baseChangeSquareHom_target q N a h
  source_trace := baseChangeSquareHom_source_trace q N a h
  target_trace := baseChangeSquareHom_target_trace q N a h
  projection_eq := baseChangeSquareHom_projection q N a h

end SerrePositivity.KST.LocalizingInvariants.SquareZero
