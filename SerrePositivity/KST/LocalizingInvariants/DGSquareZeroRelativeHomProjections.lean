module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeEndpointTransfer
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessMapOver
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquarePrecomp

/-!
概要：底付き移送と端点移送の全射を、定義展開を要しない等式として公開する。
方針：構造体の射の成分だけを取り出す。
規約：元の全射を保持。使われ方：具体的な Γ の底変更 lift と元の経路の照合。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitness
variable {R : Type u} [CommRing R] {B C W : Mon (Complex R)}
  {N : Bimod B B} {M : Bimod C C} {q q' : W ⟶ B}
  {a b a' b' : W ⟶ algebra B N}

lemma mapOver_hom (v : RelativeWitness q N a b) (f : B ⟶ C)
    (k : algebra B N ⟶ algebra C M) (hk : k ≫ projection C M = projection B N ≫ f) :
    (v.mapOver f k hk).hom = v.hom ≫ DGAlgebra.Path.map R k := rfl

lemma transferEndpoints_hom (v : RelativeWitness q N a b)
    (v' : RelativeWitness q' N a' b') (h : v.hom = v'.hom)
    (w : RelativeWitness q N a b) : (v.transferEndpoints v' h w).hom = w.hom := rfl

end SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitness

namespace SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitnessSquare
variable {R : Type u} [CommRing R] {B W : Mon (Complex R)} {N : Bimod B B}
  {q q' : W ⟶ B} {a b a' b' : W ⟶ algebra B N}
  {v w : RelativeWitness q N a b}

lemma rebase_hom (h : RelativeWitnessSquare v w) (e : q = q') :
    (h.rebase e).hom = h.hom := rfl

lemma reindex_hom (h : RelativeWitnessSquare v w)
    (v' w' : RelativeWitness q' N a' b') (hv : v.hom = v'.hom) (hw : w.hom = w'.hom) :
    (h.reindex v' w' hv hw).hom = h.hom := rfl

end SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitnessSquare
