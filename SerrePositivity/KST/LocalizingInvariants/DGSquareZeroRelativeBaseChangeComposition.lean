module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessBaseChange
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroBaseChangeDoublePath

/-!
概要：同じ指定共通底への相対経路の持ち上げが、全経路の一致・合成・反転を保つ。
方針：底と元の class への全経路射影の一意性と、実 affine 式を使う。
規約：両端の proof の選択に依存しない。使われ方：三経路貼合せの P 上での同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Preadditive
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable {R : Type u} [CommRing R] {A B W : Mon (Complex R)} (q : A ⟶ B) (N : Bimod B B)
  (a : W ⟶ A) {x y z : W ⟶ algebra B N}

lemma baseChangeRelativeWitness_congr_hom (v w : RelativeWitness (a ≫ q) N x y)
    (h : v.hom = w.hom) :
    (baseChangeRelativeWitness q N a v).hom = (baseChangeRelativeWitness q N a w).hom := by
  apply baseChangePath_hom_ext q N
  · exact (baseChangeRelativeWitness q N a v).projection_eq.trans
      (baseChangeRelativeWitness q N a w).projection_eq.symm
  · rw [baseChangeRelativeWitness_map, baseChangeRelativeWitness_map, h]

lemma baseChangeRelativeWitness_comp_hom (v : RelativeWitness (a ≫ q) N x y)
    (w : RelativeWitness (a ≫ q) N y z) :
    (baseChangeRelativeWitness q N a (v.comp w)).hom =
      ((baseChangeRelativeWitness q N a v).comp (baseChangeRelativeWitness q N a w)).hom := by
  apply baseChangePath_hom_ext q N
  · exact (baseChangeRelativeWitness q N a (v.comp w)).projection_eq.trans
      ((baseChangeRelativeWitness q N a v).comp
        (baseChangeRelativeWitness q N a w)).projection_eq.symm
  · rw [baseChangeRelativeWitness_map]
    apply Mon.Hom.ext
    rw [Mon.comp_hom', RelativeWitness.comp_hom_linear
      (baseChangeRelativeWitness q N a v) (baseChangeRelativeWitness q N a w)]
    simp only [add_comp, sub_comp, ← Mon.comp_hom']
    rw [baseChangeRelativeWitness_map, baseChangeRelativeWitness_map]
    simp only [Category.assoc, DGAlgebra.Path.diagonal_naturality,
      reassoc_of% (baseChangeLift_map q N a y v.target_projection)]
    exact RelativeWitness.comp_hom_linear v w

lemma baseChangeRelativeWitness_reverse_hom (v : RelativeWitness (a ≫ q) N x y) :
    (baseChangeRelativeWitness q N a v.reverse).hom =
      (baseChangeRelativeWitness q N a v).reverse.hom := by
  apply baseChangePath_hom_ext q N
  · exact (baseChangeRelativeWitness q N a v.reverse).projection_eq.trans
      (baseChangeRelativeWitness q N a v).reverse.projection_eq.symm
  · rw [baseChangeRelativeWitness_map]
    apply Mon.Hom.ext
    rw [Mon.comp_hom', RelativeWitness.reverse_hom_linear (baseChangeRelativeWitness q N a v)]
    simp only [add_comp, sub_comp, ← Mon.comp_hom']
    rw [baseChangeRelativeWitness_map]
    simp only [Category.assoc, DGAlgebra.Path.diagonal_naturality,
      reassoc_of% (baseChangeLift_map q N a x v.source_projection),
      reassoc_of% (baseChangeLift_map q N a y v.target_projection)]
    exact RelativeWitness.reverse_hom_linear v

end SerrePositivity.KST.LocalizingInvariants.SquareZero
