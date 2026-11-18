module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.TensorUnitAdjacent
public import SerrePositivity.EInfinity.BarrattEccles.Theory.ZeroArity
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyAdjacentTail
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyGeneratorMap

/-!
# 零入力係数の有限族の隣接交換

## 概要
HA 3.2.4.7 の二色比較で、消去する入力に代入する零入力係数の交換を計算する。

## 方針
E(0) とテンソル単位の指定同型と、有限族からテンソル冪への生成射の自然性を使う。

## 規約
有限族の隣接交換を、既存の零入力の増大の同型を使って恒等射と同定する。

## 使われ方
先頭の入力を零入力へ代入する係数射の外側等変性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable (A : Type u) [CommRing A]

/-- 実際の零入力の複体とテンソル単位との、指定増大による同型。 -/
def nullaryCoefficientIso : complex A 0 ≅ 𝟙_ (Complex A) := by
  have := zeroArity_augmentation_isIso A
  exact asIso (complexAugmentation A 0)

/-- 零入力係数の有限族の隣接交換は恒等射。 -/
lemma nullaryFamilyAdjacent_hom (n : ℕ) (i : Fin n) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentIso n (fun _ : Fin (n + 1) => complex A 0) i).hom = 𝟙 _ := by
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentIso_generator (complex A 0) n
    (fun _ : Fin (n + 1) => complex A 0) (fun _ => 𝟙 _) i
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator_asMap, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap_id, Category.id_comp] at h
  rw [adjacent_hom_eq_id_of_isoUnit (nullaryCoefficientIso A), Category.comp_id] at h
  apply (cancel_mono (eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_const (complex A 0) (n + 1)))).mp
  simpa only [Category.id_comp] using h

end SerrePositivity.EInfinity.BarrattEccles
