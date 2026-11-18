module

public import SerrePositivity.EInfinity.BarrattEccles.HomologyComposition

/-!
# 選んだ E の零次演算の部分合成ホモトピー

概要：BF §1・BM §1 の arity ごとの収縮を使い、選んだ演算の二段作用を比較する。
方針：合成係数の augmentation が一であることを証明し、同じ係数へのホモトピーで結ぶ。
規約：全 arity・全入力位置、始域の cofibrancy は不要。
使われ方：H⁰ の積の単位則・結合則。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

/-- 概要：augmentation が一である二係数の合成も一となる（BF §1、BM §1）。
方針：augmentation の部分合成保存とテンソル射の合成則を使う。
規約：全 arity と全位置、零入力を含む。
使われ方：合成係数と標準係数のホモトピー比較。 -/
lemma coefficientComposite_augmentation (m n : ℕ) (i : Fin (m + 1))
    (a : 𝟙_ (Complex A) ⟶ (operad A).arity (m + 1))
    (b : 𝟙_ (Complex A) ⟶ (operad A).arity n)
    (ha : a ≫ (augmentation A).map.app (FiniteBijection.of (m + 1)) = 𝟙 _)
    (hb : b ≫ (augmentation A).map.app (FiniteBijection.of n) = 𝟙 _) :
    coefficientComposite m n i a b ≫
      (augmentation A).map.app (FiniteBijection.of (m + n)) = 𝟙 _ := by
  simp only [coefficientComposite, Category.assoc]
  rw [(augmentation A).comp, tensorHom_comp_tensorHom_assoc, ha, hb]
  change (λ_ (𝟙_ (Complex A))).inv ≫
    (𝟙 (𝟙_ (Complex A)) ⊗ₘ 𝟙 (𝟙_ (Complex A))) ≫ (λ_ (𝟙_ (Complex A))).hom = _
  simp only [id_tensorHom, whiskerLeft_id, Category.id_comp, Iso.inv_hom_id]

/-- 概要：係数ホモトピーは全 arity の作用のホモトピーを与える（BF §1）。
方針：係数ホモトピーを入力冪とテンソルし、単位子と代数作用を合成する。
規約：実際の非有界複体射の鎖ホモトピー。
使われ方：合成係数と選んだ零次演算の作用を比較する。 -/
def coefficientOperationHomotopy (X : (operad A).Algebra) (n : ℕ)
    {a b : 𝟙_ (Complex A) ⟶ (operad A).arity n} (h : Homotopy a b) :
    Homotopy (coefficientOperation X n a) (coefficientOperation X n b) := by
  have ht := SerrePositivity.cochainTensorHomotopyLeft h (𝟙 (power X.carrier n))
  change Homotopy (a ⊗ₘ 𝟙 (power X.carrier n)) (b ⊗ₘ 𝟙 (power X.carrier n)) at ht
  simp only [tensorHom_id] at ht
  simpa only [coefficientOperation, Category.assoc] using
    (ht.compLeft (λ_ (power X.carrier n)).inv).compRight (X.action n)

/-- 概要：選んだ E 代数の全零次演算は部分合成をホモトピーで保つ（BF §1）。
方針：合成係数の augmentation と実際の代数の部分合成則を使う。
規約：零入力も含む全 arity・全位置の作用。
使われ方：H⁰ の単位則・結合則の共通の比較ホモトピー。 -/
def homologyCompositionHomotopy (X : (operad A).Algebra) (m n : ℕ) (i : Fin (m + 1)) :
    Homotopy (homologyOperation X (m + n))
      ((λ_ (power X.carrier (m + n))).inv ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction X.carrier (𝟙_ (Complex A)) m n i
          ((aritySection A n ▷ power X.carrier n) ≫ X.action n) ≫
        homologyOperation X (m + 1)) := by
  have hc := coefficientHomotopy A (m + n) (aritySection A (m + n))
    (coefficientComposite m n i (aritySection A (m + 1)) (aritySection A n))
    ((aritySection_augmentation A (m + n)).trans
      (coefficientComposite_augmentation m n i _ _
        (aritySection_augmentation A (m + 1)) (aritySection_augmentation A n)).symm)
  exact (coefficientOperationHomotopy X (m + n) hc).trans
    (Homotopy.ofEq (coefficientOperation_comp X m n i _ _))

end SerrePositivity.EInfinity.BarrattEccles
