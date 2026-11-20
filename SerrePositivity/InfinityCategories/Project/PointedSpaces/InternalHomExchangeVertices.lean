module


public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeUnit

/-!
概要：内部 Hom の交換を単位からの射で評価する。
方針：二重 uncurry とテンソル交換の自然性で射の転置を計算する。
規約：一般の閉 braided 圏で述べる。
使われ方：Goerss–Jardine I §7、VIII §1。loop 族の頂点と辺の比較。
-/

@[expose] public section
universe v u
open CategoryTheory MonoidalCategory MonoidalClosed

namespace SerrePositivity.KST.Spectra.InternalHomExchange
end SerrePositivity.KST.Spectra.InternalHomExchange
namespace SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeVertices
open _root_.SerrePositivity.KST.Spectra.InternalHomExchange

noncomputable section
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C]

/-- 単位からの射に内部 Hom の交換を施すと、元の射の転置を表す。 -/
lemma curry'_hom {A K Y : C} (f : A ⟶ (ihom K).obj Y) :
    curry' f ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A K Y).hom =
      curry' (curry ((β_ A K).hom ≫ uncurry f)) := by
  apply uncurry_injective
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.uncurry_uncurry_hom,
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange_natural_right_assoc]
  have he : A ◁ curry' f ≫ (ihom.ev A).app ((ihom K).obj Y) =
      (ρ_ A).hom ≫ f := by
    change uncurry (curry' f) = _
    rw [curry', uncurry_curry]
  rw [← whiskerLeft_comp_assoc, he, whiskerLeft_comp, Category.assoc]
  rw [curry', uncurry_curry, uncurry_natural_left, uncurry_curry]
  have hu : (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange A K (𝟙_ C)).hom ≫ K ◁ (ρ_ A).hom =
      A ◁ (ρ_ K).hom ≫ (β_ A K).hom := by
    simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, tensorRight, Functor.flip, curriedTensor]
    monoidal
  rw [← Category.assoc, ← Category.assoc, hu, uncurry_eq]
  simp only [Category.assoc]

end
end SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeVertices

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
