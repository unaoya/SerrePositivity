module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength

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
end SerrePositivity.KST.Spectra.HomTensorStrength
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrengthPoint
open _root_.SerrePositivity.KST.Spectra.HomTensorStrength
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C]

/-- 一つの射で固定した strength は、その射とのテンソルの curry。 -/
lemma point (K A Y : C) (f : A ⟶ Y) :
    (ρ_ K).inv ≫ K ◁ curry' f ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map K A Y =
      curry ((β_ A K).hom ≫ K ◁ f) := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map, uncurry_curry, uncurry_curry,
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange_natural_right_assoc, ← whiskerLeft_comp]
  change A ◁ (ρ_ K).inv ≫ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange A K (𝟙_ C)).hom ≫
    K ◁ uncurry (curry' f) = _
  rw [curry', uncurry_curry, whiskerLeft_comp, ← Category.assoc, ← Category.assoc]
  congr 1
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    tensorRight, Functor.flip, curriedTensor]
  monoidal

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrengthPoint

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.HomTensorStrength.point := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrengthPoint.point
