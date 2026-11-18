module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.NullaryPrefixDelete
public import SerrePositivity.EInfinity.BarrattEccles.Theory.OperadMorphismComposition
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CommutativeComposition
public import SerrePositivity.EInfinity.BarrattEccles.OperadAugmentation

/-!
# 零入力への係数射影と指定増大

## 概要
HA 3.2.4.7 の二色係数比較の各射影が、実際の Barratt–Eccles の増大を保つことを示す。

## 方針
オペラッド射の反復合成の自然性を使い、可換オペラッドでは単位族の縮約で計算する。

## 規約
零入力の単位と増大の合成は、指定された厳密な同型の逆の相殺で扱う。

## 使われ方
二色の指定係数比較に解像度の比較定理を適用する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
open scoped BigOperators
attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level

/-- 単位からの係数族の挿入と、両因子の射との指定された比較。 -/
@[reassoc]
lemma coefficientUnitInsert_map {A : Type u} [CommRing A] {X Y V W : Complex A}
    (η : 𝟙_ (Complex A) ⟶ V) (a : X ⟶ Y) (b : V ⟶ W) :
    coefficientUnitInsert X V η ≫ (a ⊗ₘ b) =
      a ≫ coefficientUnitInsert Y W (η ≫ b) := by
  simp only [coefficientUnitInsert, Category.assoc]
  rw [whiskerLeft_comp_tensorHom, tensorHom_def, ← rightUnitor_inv_naturality_assoc]

namespace BarrattEccles
variable (A : Type u) [CommRing A]
attribute [local implicit_reducible] operad sequence

/-- 零入力の指定族を増大に通すと、元の単位族の縮約の逆射になる。 -/
lemma nullaryInputFamily_augmentation (n : ℕ) :
    nullaryInputFamily A n ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun _ => (augmentation A).map.app (FiniteBijection.of 0)) =
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitFamilyIso A n).inv := by
  have h : (augmentation A).map.app (FiniteBijection.of 0) =
      (nullaryCoefficientIso A).hom := by
    rw [augmentation_app]
    rfl
  rw [h]
  unfold nullaryInputFamily
  rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap_comp]
  simp only [Iso.inv_hom_id, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap_id, Category.comp_id]

/-- 先頭の入力を零入力へ代入する指定射は、実際の増大を保つ。 -/
lemma nullaryPrefixDelete_augmentation (n k : ℕ) :
    nullaryPrefixDelete A n k ≫ (augmentation A).map.app (FiniteBijection.of k) =
      (augmentation A).map.app (FiniteBijection.of (n + k)) := by
  let hsum : (∑ _ : Fin n, 0) + k = k := by simp
  have he : eqToHom (congrArg (operad A).arity hsum) ≫
      (augmentation A).map.app (FiniteBijection.of k) =
      (augmentation A).map.app (FiniteBijection.of ((∑ _ : Fin n, 0) + k)) := by
    have h := Operad.Hom.component_index_eq (augmentation A) hsum
    dsimp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.commutativeOperad, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.arity, SerrePositivity.SymmetricSequence.level] at h
    simpa only [eqToHom_refl, Category.comp_id] using h
  unfold nullaryPrefixDelete
  simp only [Category.assoc]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.arity, SerrePositivity.SymmetricSequence.level] at he ⊢
  rw [he, ← Operad.Hom.composeFirstInputs_naturality,
    coefficientUnitInsert_map_assoc, nullaryInputFamily_augmentation,
    commutativeComposeFirstInputs_eq]
  simp only [coefficientUnitInsert, Category.assoc]
  change (augmentation A).map.app (FiniteBijection.of (n + k)) ≫
    (ρ_ (𝟙_ (Complex A))).inv ≫
      ((𝟙_ (Complex A)) ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitFamilyIso A n).inv) ≫
        ((𝟙_ (Complex A)) ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitFamilyIso A n).hom) ≫
          (ρ_ (𝟙_ (Complex A))).hom = _
  rw [← whiskerLeft_comp_assoc, Iso.inv_hom_id, whiskerLeft_id, Category.id_comp,
    Iso.inv_hom_id, Category.comp_id]

end BarrattEccles
end SerrePositivity.EInfinity
