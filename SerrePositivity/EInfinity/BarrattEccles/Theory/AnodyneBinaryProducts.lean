module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneLocalizedTensor
public import Mathlib.CategoryTheory.Localization.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Anodyne 局所化と二項の積

概要：HA 3.2.4.7 の Hom の積比較で、局所化された同型の積を扱う。
方針：二項積での anodyne の安定性を通常の局所化の積保存へ渡す。
規約：単体集合のモデル構造を仮定しない。
使われ方：DK と Map^h の自然同型を二項積に適用する。［一般∞］の移動候補。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.SimplicialModel

/-- 関手の積比較は、指定された組への射を保つ。 -/
lemma mapPairing_prodComparison {C : Type u} [Category.{v} C]
    {D : Type*} [Category D] (F : C ⥤ D) {X Y Z : C}
    [HasBinaryProduct Y Z] [HasBinaryProduct (F.obj Y) (F.obj Z)]
    (f : X ⟶ Y) (g : X ⟶ Z) :
    F.map (prod.lift f g) ≫ prodComparison F Y Z = prod.lift (F.map f) (F.map g) := by
  apply prod.hom_ext
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun t => F.map (prod.lift f g) ≫ t)
        (Limits.prodComparison_fst F Y Z)).trans
          (((F.map_comp _ _).symm.trans (congrArg F.map (prod.lift_fst f g))).trans
            (prod.lift_fst (F.map f) (F.map g)).symm))
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun t => F.map (prod.lift f g) ≫ t)
        (Limits.prodComparison_snd F Y Z)).trans
          (((F.map_comp _ _).symm.trans (congrArg F.map (prod.lift_snd f g))).trans
            (prod.lift_snd (F.map f) (F.map g)).symm))

/-- 二点集合を添字とする積と指定二項積の同型。 -/
def walkingPairProductIso {C : Type u} [Category.{v} C] [HasBinaryProducts C]
    (F : WalkingPair → C) : (∏ᶜ F) ≅ F .left ⨯ F .right where
  hom := prod.lift (Pi.π F .left) (Pi.π F .right)
  inv := Pi.lift (fun j => match j with | .left => prod.fst | .right => prod.snd)
  hom_inv_id := by apply Pi.hom_ext; intro j; cases j <;> simp
  inv_hom_id := by apply prod.hom_ext <;> simp

/-- 二点添字の指定同型は、因子ごとの指定射を保つ。 -/
lemma walkingPairProductIso_naturality {C : Type u} [Category.{v} C] [HasBinaryProducts C]
    (F G : WalkingPair → C) (f : ∀ j, F j ⟶ G j) :
    Limits.Pi.map f ≫ (walkingPairProductIso G).hom =
      (walkingPairProductIso F).hom ≫ prod.map (f .left) (f .right) := by
  apply prod.hom_ext <;> simp [walkingPairProductIso]

/-- 単体集合の指定テンソル積と、圏論の選ばれた二項積を比較する。 -/
def simplicialTensorProdIso (X Y : SSet.{u}) : X ⊗ Y ≅ X ⨯ Y where
  hom := prod.lift (CartesianMonoidalCategory.fst X Y) (CartesianMonoidalCategory.snd X Y)
  inv := CartesianMonoidalCategory.lift prod.fst prod.snd
  hom_inv_id := by apply CartesianMonoidalCategory.hom_ext <;> simp
  inv_hom_id := by apply prod.hom_ext <;> simp

/-- 二種類の積の比較は、両因子の指定射を保つ。 -/
lemma simplicialTensorProdIso_naturality {X X' Y Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    (simplicialTensorProdIso X Y).hom ≫ prod.map f g =
      (f ⊗ₘ g) ≫ (simplicialTensorProdIso X' Y').hom := by
  apply prod.hom_ext <;> simp [simplicialTensorProdIso]

/-- 二つの anodyne の積も anodyne。 -/
lemma anodyne_binaryProductMap {X X' Y Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y')
    (hf : SSet.anodyneExtensions f) (hg : SSet.anodyneExtensions g) :
    SSet.anodyneExtensions (prod.map f g) := by
  have he : prod.map f g = (simplicialTensorProdIso X Y).inv ≫
      (f ⊗ₘ g) ≫ (simplicialTensorProdIso X' Y').hom := by
    rw [Iso.eq_inv_comp, simplicialTensorProdIso_naturality]
  rw [he]
  apply SSet.anodyneExtensions.comp_mem _ _ (SSet.anodyneExtensions.of_isIso _)
  apply SSet.anodyneExtensions.comp_mem _ _ _ (SSet.anodyneExtensions.of_isIso _)
  rw [tensorHom_def]
  exact SSet.anodyneExtensions.comp_mem _ _ (hf.whiskerRight Y) (hg.whiskerLeft X')

/-- Anodyne は二点添字の積に安定。 -/
instance anodyne_stableUnderWalkingPairProducts :
    SSet.anodyneExtensions.{u}.IsStableUnderProductsOfShape WalkingPair := by
  apply MorphismProperty.IsStableUnderProductsOfShape.mk
  intro F G _ _ f hf
  have he : Limits.Pi.map f = (walkingPairProductIso F).hom ≫
      prod.map (f .left) (f .right) ≫ (walkingPairProductIso G).inv := by
    rw [← Category.assoc, Iso.eq_comp_inv, walkingPairProductIso_naturality]
  rw [he]
  exact SSet.anodyneExtensions.comp_mem _ _ (SSet.anodyneExtensions.of_isIso _)
    (SSet.anodyneExtensions.comp_mem _ _ (anodyne_binaryProductMap _ _ (hf _) (hf _))
      (SSet.anodyneExtensions.of_isIso _))

/-- Anodyne 局所化の値圏に二項積を選ぶ。 -/
instance anodyneLocalization_hasBinaryProducts :
    HasBinaryProducts (SSet.anodyneExtensions.{u}.Localization) :=
  Localization.hasProductsOfShape AnodyneHomotopy.anodyneQ SSet.anodyneExtensions WalkingPair

/-- 局所化は指定二項積を保存する。 -/
instance anodyneQ_preservesBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair) AnodyneHomotopy.anodyneQ.{u} :=
  Localization.preservesProductsOfShape AnodyneHomotopy.anodyneQ SSet.anodyneExtensions WalkingPair

end SerrePositivity.EInfinity
