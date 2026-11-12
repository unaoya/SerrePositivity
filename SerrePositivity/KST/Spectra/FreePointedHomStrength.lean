module

public import SerrePositivity.KST.Spectra.FreePointedHomEvaluation
public import SerrePositivity.KST.Spectra.PointedSmashExchange

/-!
概要：自由基点の Hom の strength の基礎単体集合上での評価公式。
方針：自由基点の制限と smash 商の三因子交換の式を、点つき評価の自然性へ合成する。
規約：全パラメータの厳密な等式。使われ方：元の weighted Hom end の作用の忘却。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.FreePointedHomRestriction
open PointedSimplicialSet

/-- 自由基点の Hom の strength を忘れると、通常の評価と元の smash 合成になる。 -/
lemma strength_evaluation (W : SSet.{u}) (K B Y : PointedSimplicialSet.{u}) (f : K ⊗ B ⟶ Y) :
    uncurry (productToSmash K (PointedObject.basedHom (PointedObject.adjoin W) B) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map K (PointedObject.adjoin W) B ≫
          (ihom (PointedObject.adjoin W)).map f).right ≫
        FreePointedHomRestriction.restrict W Y) =
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange W K.right
        (PointedObject.basedHom (PointedObject.adjoin W) B).right).hom ≫
        K.right ◁ uncurry (FreePointedHomRestriction.restrict W B) ≫
          productToSmash K B ≫ f.right := by
  rw [uncurry_natural_left, FreePointedHomRestriction.uncurry_restrict,
    uncurry_natural_right, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map, uncurry_curry]
  simp only [Under.comp_right, Category.assoc]
  erw [whisker_exchange_assoc]
  erw [PointedSmashExchange.exchange_assoc]
  have hn := productToSmash_naturality (𝟙 K)
    ((ihom.ev (PointedObject.adjoin W)).app B)
  simp only [Under.id_right, id_tensorHom] at hn
  erw [← reassoc_of% hn, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange_natural_left_assoc]
  rw [FreePointedHomRestriction.restrict_evaluation]
  simp only [whiskerLeft_comp, Category.assoc]
  rfl

/-- 自由基点の Hom への任意のパラメータ族を通した strength の評価公式。 -/
lemma strength_evaluation_parameter (W : SSet.{u})
    (K B Y P : PointedSimplicialSet.{u})
    (q : P ⟶ PointedObject.basedHom (PointedObject.adjoin W) B) (f : K ⊗ B ⟶ Y) :
    uncurry (productToSmash K P ≫
        ((𝟙 K ⊗ₘ q) ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map K (PointedObject.adjoin W) B ≫
          (ihom (PointedObject.adjoin W)).map f).right ≫ restrict W Y) =
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange W K.right P.right).hom ≫
        K.right ◁ uncurry (q.right ≫ restrict W B) ≫ productToSmash K B ≫ f.right := by
  simp only [Under.comp_right, Category.assoc]
  rw [← Category.assoc (productToSmash K P),
    ← productToSmash_naturality (𝟙 K) q]
  simp only [Under.id_right, id_tensorHom, Category.assoc]
  rw [uncurry_natural_left]
  have h := strength_evaluation W K B Y f
  change uncurry (productToSmash K (PointedObject.basedHom (PointedObject.adjoin W) B) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map K (PointedObject.adjoin W) B).right ≫
      ((ihom (PointedObject.adjoin W)).map f).right ≫ restrict W Y) = _ at h
  rw [h, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange_natural_right_assoc]
  simp only [uncurry_natural_left, whiskerLeft_comp, Category.assoc]

end SerrePositivity.KST.Spectra.FreePointedHomRestriction
