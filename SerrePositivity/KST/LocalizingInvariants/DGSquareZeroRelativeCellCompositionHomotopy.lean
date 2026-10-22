module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeCellPathOperations
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroCellTransportHomotopy

/-!
概要：同じ全射準同型上の直接経路と二経路の合成が誘導する実 class 輸送を比較する。
方針：底を固定する実 cell 合成を構成し、直接経路と同じ端点の二重充填へ渡す。
規約：比較する二つ目の経路や class 二重経路の存在を追加入力しない。使われ方：自然性合成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
open DGAlgebra
variable (R : Type u) [CommRing R] {W C B : Mon (Complex R)} (p : C ⟶ B)
  (hs : ∀ n : ℤ, Function.Surjective (p.hom.f n)) (hq : QuasiIso p.hom)
  {f g h : W ⟶ C} (u : DGAlgebra.Path.Witness R f h) (v : DGAlgebra.Path.Witness R f g)
  (w : DGAlgebra.Path.Witness R g h)
  (hu : u.hom ≫ DGAlgebra.Path.map R p = (f ≫ p) ≫ DGAlgebra.Path.diagonal R B)
  (hv : v.hom ≫ DGAlgebra.Path.map R p = (f ≫ p) ≫ DGAlgebra.Path.diagonal R B)
  (hw : w.hom ≫ DGAlgebra.Path.map R p = (g ≫ p) ≫ DGAlgebra.Path.diagonal R B)
  (N : Bimod B B) (κ : C ⟶ SquareZero.algebra B N) (hκ : κ ≫ SquareZero.projection B N = p)

include hu in
lemma relativeCellComposition_direct_relative :
    (u.precomp (cellAugmentation R W)).hom ≫ DGAlgebra.Path.map R p =
      ((cellAugmentation R W ≫ f) ≫ p) ≫ DGAlgebra.Path.diagonal R B := by
  change (cellAugmentation R W ≫ u.hom) ≫ DGAlgebra.Path.map R p = _
  rw [Category.assoc, hu]
  simp only [Category.assoc]

def relativeCellCompositionTransportHomotopy : DGAlgebra.Path.Witness R
    (transport N (SquareZero.cellClassWitness R p (u.precomp (cellAugmentation R W))
      (relativeCellComposition_direct_relative R p u hu) N κ hκ))
    (transport N (SquareZero.cellClassWitness R p (RelativePath.cellComp R p hs v w hv hw)
      (RelativePath.cellComp_relative R p hs v w hv hw) N κ hκ)) :=
  cellTransportHomotopy R p hs hq (u.precomp (cellAugmentation R W))
    (RelativePath.cellComp R p hs v w hv hw) (relativeCellComposition_direct_relative R p u hu)
    (RelativePath.cellComp_relative R p hs v w hv hw) N κ hκ

lemma relativeCellCompositionTransportHomotopy_left :
    (relativeCellCompositionTransportHomotopy R p hs hq u v w hu hv hw N κ hκ).hom ≫
      DGAlgebra.Path.map R (relativeLeft N (cellAugmentation R (cellResolution R W) ≫
        (cellAugmentation R W ≫ h) ≫ κ)) =
    relativeLeft N (cellAugmentation R (cellResolution R W) ≫
      (cellAugmentation R W ≫ f) ≫ κ) ≫
      DGAlgebra.Path.diagonal R (cellResolution R (cellResolution R W)) :=
  cellTransportHomotopy_left R p hs hq _ _ _ _ N κ hκ

lemma relativeCellCompositionTransportHomotopy_right :
    (relativeCellCompositionTransportHomotopy R p hs hq u v w hu hv hw N κ hκ).hom ≫
      DGAlgebra.Path.map R (relativeRight N (cellAugmentation R (cellResolution R W) ≫
        (cellAugmentation R W ≫ h) ≫ κ)) =
    relativeRight N (cellAugmentation R (cellResolution R W) ≫
      (cellAugmentation R W ≫ f) ≫ κ) ≫ DGAlgebra.Path.diagonal R B :=
  cellTransportHomotopy_right R p hs hq _ _ _ _ N κ hκ

end SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
