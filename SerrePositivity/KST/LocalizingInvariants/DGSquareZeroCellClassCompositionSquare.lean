module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroCellClassCompositionHom
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessRectangleTransport
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquareCongr

/-!
概要：cell 合成を class へ写した経路と、元の二 class 経路の affine 合成を実際に比較する。
方針：指定 cellCompLift から得た正方形の輪郭補正で定数辺を相殺する。
規約：底射には各次数全射性だけを要求。使われ方：Postnikov 自然性の二段合成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
namespace RelativeWitness
variable {R : Type u} [CommRing R] {B W : Mon (Complex R)} {N : Bimod B B}
  {q : W ⟶ B} {a b : W ⟶ algebra B N}

lemma refl_comp_hom (v : RelativeWitness q N a b) :
    ((refl a v.source_projection).comp v).hom = v.hom := by
  apply Mon.Hom.ext
  rw [comp_hom_linear]
  change (a ≫ DGAlgebra.Path.diagonal R (algebra B N)).hom -
    (a ≫ DGAlgebra.Path.diagonal R (algebra B N)).hom + v.hom.hom = v.hom.hom
  rw [sub_self, zero_add]

end RelativeWitness
open DGAlgebra
variable (R : Type u) [CommRing R] {W C B : Mon (Complex R)} (p : C ⟶ B)
  (hs : ∀ n : ℤ, Function.Surjective (p.hom.f n)) {f g h : W ⟶ C}
  (v : DGAlgebra.Path.Witness R f g) (w : DGAlgebra.Path.Witness R g h)
  (hv : v.hom ≫ DGAlgebra.Path.map R p = (f ≫ p) ≫ DGAlgebra.Path.diagonal R B)
  (hw : w.hom ≫ DGAlgebra.Path.map R p = (g ≫ p) ≫ DGAlgebra.Path.diagonal R B)
  (N : Bimod B B) (κ : C ⟶ algebra B N) (hκ : κ ≫ projection B N = p)

def relativeClassCellReflexive : RelativeWitness ((cellAugmentation R W ≫ f) ≫ p) N
    ((cellAugmentation R W ≫ f) ≫ κ) ((cellAugmentation R W ≫ f) ≫ κ) :=
  RelativeWitness.refl _ (by rw [Category.assoc, hκ])

def cellClassCompositionRectangle : RelativeWitnessRectangle
    (relativeClassCellReflexive R p N κ hκ)
    (relativeClassAffineRefined R p v hv N κ hκ w hw)
    (relativeClassCellReflexive R p N κ hκ)
    (relativeClassCellComposite R p v hv N κ hκ w hw hs) where
  hom := cellClassCompositionHom R p hs v w hv hw N κ hκ
  source_eq := cellClassCompositionHom_source R p hs v w hv hw N κ hκ
  target_eq := cellClassCompositionHom_target R p hs v w hv hw N κ hκ
  source_trace := cellClassCompositionHom_source_trace R p hs v w hv hw N κ hκ
  target_trace := cellClassCompositionHom_target_trace R p hs v w hv hw N κ hκ
  projection_eq := cellClassCompositionHom_projection R p hs v w hv hw N κ hκ

/-- 元の cell 合成と元の affine class 合成を、同じ源・底・両端で比較する実二重経路。 -/
def cellClassCompositionSquare : RelativeWitnessSquare
    (relativeClassCellComposite R p v hv N κ hκ w hw hs)
    (relativeClassAffineRefined R p v hv N κ hκ w hw) := by
  let z := (cellClassCompositionRectangle R p hs v w hv hw N κ hκ).contourSquare
  exact RelativeWitnessSquare.replacePaths z
    (RelativeWitness.refl_comp_hom (relativeClassCellComposite R p v hv N κ hκ w hw hs))
    (RelativeWitness.refl_comp_hom (relativeClassAffineRefined R p v hv N κ hκ w hw))

def cellClassCompositionTransportHomotopy : DGAlgebra.Path.Witness R
    (SquareZeroExtension.transport N (relativeClassCellComposite R p v hv N κ hκ w hw hs))
    (SquareZeroExtension.transport N (relativeClassAffineRefined R p v hv N κ hκ w hw)) :=
  SquareZeroExtension.transportHomotopy N (cellClassCompositionSquare R p hs v w hv hw N κ hκ)

end SerrePositivity.KST.LocalizingInvariants.SquareZero
