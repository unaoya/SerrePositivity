module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeEndpointTransfer
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativePathCompositionCongr

/-!
概要：参照経路の表示変更に沿い、その後に続く経路の接合端点と底を移す。
方針：参照全射の等式から終点と底を同定し、続く経路の全射を保持する。
規約：続く経路の他端は変えない。使われ方：native class 互換性への自然性の接合。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitness
variable {R : Type u} [CommRing R] {B W : Mon (Complex R)} {N : Bimod B B}
  {q q' : W ⟶ B} {a b a' b' c : W ⟶ algebra B N}
  (v : RelativeWitness q N a b) (v' : RelativeWitness q' N a' b')
  (h : v.hom = v'.hom)

def followWithEndpoints (w : RelativeWitness q N b c) : RelativeWitness q' N b' c where
  hom := w.hom
  source_eq := w.source_eq.trans (RelativeWitnessSquare.reindex_target v' h)
  target_eq := w.target_eq
  projection_eq := w.projection_eq.trans (congrArg
    (fun k => k ≫ DGAlgebra.Path.diagonal R B) (RelativeWitnessSquare.reindex_base v' h))

lemma followWithEndpoints_comp_hom (w : RelativeWitness q N b c) :
    (v'.comp (v.followWithEndpoints v' h w)).hom = (v.comp w).hom :=
  comp_congr_hom_of_paths h.symm rfl

lemma replaceHom_hom (k : W ⟶ DGAlgebra.Path.algebra R (algebra B N))
    (hk : v.hom = k) : (v.replaceHom k hk).hom = k := rfl

end SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitness
