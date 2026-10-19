module

public import SerrePositivity.KST.Spectra.HomTensorStrength

/-!
概要：内部 Hom の strength を一つの射で固定したときの評価式。
方針：uncurry と因子交換の自然性を使い、単位因子を取り除く。
規約：任意の閉 braided モノイダル圏。
使われ方：cotensor の普遍評価による前合成の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.HomTensorStrength
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C]

/-- 一つの射で固定した strength は、その射とのテンソルの curry。 -/
lemma point (K A Y : C) (f : A ⟶ Y) :
    (ρ_ K).inv ≫ K ◁ curry' f ≫ map K A Y =
      curry ((β_ A K).hom ≫ K ◁ f) := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_left, map, uncurry_curry, uncurry_curry,
    exchange_natural_right_assoc, ← whiskerLeft_comp]
  change A ◁ (ρ_ K).inv ≫ (exchange A K (𝟙_ C)).hom ≫
    K ◁ uncurry (curry' f) = _
  rw [curry', uncurry_curry, whiskerLeft_comp, ← Category.assoc, ← Category.assoc]
  congr 1
  dsimp only [exchange, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    tensorRight, Functor.flip, curriedTensor]
  monoidal

end SerrePositivity.KST.Spectra.HomTensorStrength
