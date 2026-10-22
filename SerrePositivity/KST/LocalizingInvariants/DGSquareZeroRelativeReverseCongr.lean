module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativePathCompositionCongr
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessMapOver

/-!
概要：相対経路の反転が全射の同定と源の前合成を保つことを証明する。
方針：両評価から端点を同定し、元の affine 反転式を比較する。
規約：底・端点の表示の一致を要求しない。使われ方：fixed class 互換性の右像。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Preadditive
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitness
variable {R : Type u} [CommRing R] {B W T : Mon (Complex R)} {N : Bimod B B}
  {q q' : W ⟶ B} {a b a' b' : W ⟶ algebra B N}
  {v : RelativeWitness q N a b} {w : RelativeWitness q' N a' b'}

lemma reverse_congr_hom_of_paths (h : v.hom = w.hom) : v.reverse.hom = w.reverse.hom := by
  have ha : a = a' := v.source_eq.symm.trans
    ((congrArg (fun k => k ≫ DGAlgebra.Path.source R (algebra B N)) h).trans w.source_eq)
  have hb : b = b' := v.target_eq.symm.trans
    ((congrArg (fun k => k ≫ DGAlgebra.Path.target R (algebra B N)) h).trans w.target_eq)
  apply Mon.Hom.ext
  rw [reverse_hom_linear, reverse_hom_linear, h, ha, hb]

lemma precomp_reverse_hom (v : RelativeWitness q N a b) (e : T ⟶ W) :
    (v.reverse.precomp e).hom = (v.precomp e).reverse.hom := by
  apply Mon.Hom.ext
  change (e ≫ v.reverse.hom).hom = _
  rw [Mon.comp_hom', reverse_hom_linear, reverse_hom_linear]
  simp only [comp_add, comp_sub, ← Mon.comp_hom', Category.assoc]
  rfl

variable {C : Mon (Complex R)} {M : Bimod C C} {c : W ⟶ algebra B N}

lemma precomp_mapOver_reverse_comp_hom (v : RelativeWitness q N a b)
    (w : RelativeWitness q N a c) (e : T ⟶ W)
    (f : B ⟶ C) (k : algebra B N ⟶ algebra C M)
    (hk : k ≫ projection C M = projection B N ≫ f) :
    (((v.reverse.comp w).precomp e).mapOver f k hk).hom =
      (((v.precomp e).mapOver f k hk).reverse.comp
        ((w.precomp e).mapOver f k hk)).hom := by
  have hp := (precomp_comp_hom v.reverse w e).trans
    (comp_congr_hom_of_paths (precomp_reverse_hom v e) rfl)
  have hm := congrArg (fun t => t ≫ DGAlgebra.Path.map R k) hp
  exact hm.trans ((mapOver_comp_hom f k hk (v.precomp e).reverse (w.precomp e)).trans
    (comp_congr_hom_of_paths (mapOver_reverse_hom f k hk (v.precomp e)) rfl))

end SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitness
