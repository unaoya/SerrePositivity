module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroAffinePath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathMapAffine

/-!
概要：底を保つ affine 経路の underlying 射を計算し、厳密な相殺と実経路証人を得る。
方針：経路射の affine 自然性を三重 pullback の三射影で計算する。
規約：底への全経路の一致を入力する。使われ方：class 経路の補正と逆三角形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Preadditive
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable (R : Type u) [CommRing R] {B W : Mon (Complex R)} (N : Bimod B B)
  (a b c : W ⟶ DGAlgebra.Path.algebra R (algebra B N))
  (hab : a ≫ DGAlgebra.Path.map R (projection B N) = b ≫ DGAlgebra.Path.map R (projection B N))
  (hac : a ≫ DGAlgebra.Path.map R (projection B N) = c ≫ DGAlgebra.Path.map R (projection B N))

lemma affinePathHom_linear : (affinePathHom R N a b c hab hac).hom = a.hom - b.hom + c.hom := by
  rw [affinePathHom, Mon.comp_hom', DGAlgebra.Path.map_affine R (affineFirst B N)
    (affineMiddle B N) (affineLast B N) (affineOperation B N) (affineOperation_linear B N),
    comp_add, comp_sub]
  change ((affineTriplePath R N a b c hab hac ≫ DGAlgebra.Path.map R (affineFirst B N)).hom -
    (affineTriplePath R N a b c hab hac ≫ DGAlgebra.Path.map R (affineMiddle B N)).hom +
    (affineTriplePath R N a b c hab hac ≫ DGAlgebra.Path.map R (affineLast B N)).hom) = _
  rw [affineTriplePath_first, affineTriplePath_middle, affineTriplePath_last]

lemma affinePathHom_cancel_right : affinePathHom R N a b b hab hab = a := by
  apply Mon.Hom.ext
  rw [affinePathHom_linear, sub_add_cancel]

lemma affinePathHom_cancel_left : affinePathHom R N a a c rfl hac = c := by
  apply Mon.Hom.ext
  rw [affinePathHom_linear, sub_self, zero_add]

section Witness
variable (q : W ⟶ B) (s₀ s₁ t₀ t₁ u₀ u₁ : W ⟶ algebra B N)
  (hs₀ : s₀ ≫ projection B N = q) (hs₁ : s₁ ≫ projection B N = q)
  (ht₀ : t₀ ≫ projection B N = q) (ht₁ : t₁ ≫ projection B N = q)
  (hu₀ : u₀ ≫ projection B N = q) (hu₁ : u₁ ≫ projection B N = q)
  (ws : DGAlgebra.Path.Witness R s₀ s₁) (wt : DGAlgebra.Path.Witness R t₀ t₁)
  (wu : DGAlgebra.Path.Witness R u₀ u₁)
  (hst : ws.hom ≫ DGAlgebra.Path.map R (projection B N) =
    wt.hom ≫ DGAlgebra.Path.map R (projection B N))
  (hsu : ws.hom ≫ DGAlgebra.Path.map R (projection B N) =
    wu.hom ≫ DGAlgebra.Path.map R (projection B N))

def affineWitness : DGAlgebra.Path.Witness R
    (affineMapOver q N s₀ t₀ u₀ hs₀ ht₀ hu₀) (affineMapOver q N s₁ t₁ u₁ hs₁ ht₁ hu₁) where
  hom := affinePathHom R N ws.hom wt.hom wu.hom hst hsu
  source_eq := by
    apply Mon.Hom.ext
    rw [affinePathHom_source_linear, ws.source_eq, wt.source_eq, wu.source_eq,
      affineMapOver_linear]
  target_eq := by
    apply Mon.Hom.ext
    rw [affinePathHom_target_linear, ws.target_eq, wt.target_eq, wu.target_eq,
      affineMapOver_linear]

lemma affineWitness_projection :
    (affineWitness R N q s₀ s₁ t₀ t₁ u₀ u₁ hs₀ hs₁ ht₀ ht₁ hu₀ hu₁ ws wt wu hst hsu).hom ≫
      DGAlgebra.Path.map R (projection B N) = ws.hom ≫ DGAlgebra.Path.map R (projection B N) :=
  affinePathHom_projection R N ws.hom wt.hom wu.hom hst hsu

end Witness
end SerrePositivity.KST.LocalizingInvariants.SquareZero
