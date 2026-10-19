module

public import SerrePositivity.EInfinity.AlexanderWhitney.ChainDiagonal

/-!
# AW 対角の余単位

概要：Berger–Fresse §1.1.4 の頂点 augmentation を鎖写像へ束ね、余単位則を証明する。
方針：一次の境界の両端が同じ値を持つことと、零次因子への射影を用いる。
規約：余単位の終域は自然数鎖複体のテンソル単位である。
使われ方：AW の余代数構造と Barratt–Eccles の Hopf 構造。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.AlexanderWhitney

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex

variable (A : Type u) [CommRing A]

/-- 概要：頂点 augmentation は一次境界を消す（Berger–Fresse §1.1.4）。
方針：生成元の境界の二項を同じ値の逆符号の和として計算する。
規約：基礎環の標数を制限しない。
使われ方：augmentation を鎖写像にする条件。 -/
lemma d_vertexAugmentation (X : SSet.{0}) :
    (chains A X).d 1 0 ≫ vertexAugmentation A X = 0 := by
  apply generator_hom_ext A X 1
  intro x
  change vertexAugmentation A X ((chains A X).d (0 + 1) 0 (generator A X 1 x)) = 0
  rw [generator_d]
  simp [Fin.sum_univ_two]

/-- 概要：AW の余単位となる augmentation 鎖写像（Berger–Fresse §1.1.4）。
方針：零次の頂点 augmentation を single₀ への射へ延長する。
規約：正次数の成分は零である。
使われ方：AW 対角の左右の余単位則を記述する。 -/
def counit (X : SSet.{0}) : chains A X ⟶ HomologicalComplex.tensorUnit (ModuleCat A) (.down ℕ) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨vertexAugmentation A X, d_vertexAugmentation A X⟩

/-- 概要：余単位鎖写像の零次成分（Berger–Fresse §1.1.4）。
方針：single₀ への延長の零次評価を使う。
規約：零次の単位複体は係数環の単位加群である。
使われ方：次数成分の余単位則を鎖写像へ移す。 -/
@[simp] lemma counit_f_zero (X : SSet.{0}) :
    (counit A X).f 0 = vertexAugmentation A X :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

private lemma diagonal_counit_left_inv (X : SSet.{0}) :
    diagonal A X ≫ HomologicalComplex.tensorHom (counit A X) (𝟙 (chains A X)) =
      (HomologicalComplex.leftUnitor (chains A X)).inv := by
  apply HomologicalComplex.hom_ext
  intro n
  apply tensorProjection_hom_ext
  intro p q hpq
  by_cases hp : p = 0
  · subst p
    have hq : q = n := by omega
    subst q
    simp only [HomologicalComplex.comp_f, Category.assoc, tensorHom_projection,
      diagonal_projection_assoc, HomologicalComplex.id_f, MonoidalCategory.tensorHom_id,
      counit_f_zero]
    change component A X n 0 n _ ≫ (vertexAugmentation A X ▷ (chains A X).X n) =
      (HomologicalComplex.leftUnitor' (chains A X)).inv n ≫ _
    rw [HomologicalComplex.leftUnitor'_inv]
    have hz : (singleObjXSelf (.down ℕ) 0 (𝟙_ (ModuleCat A))).inv ▷ (chains A X).X n =
        𝟙 ((𝟙_ (ModuleCat A)) ⊗ (chains A X).X n) := by
      change (𝟙 (𝟙_ (ModuleCat A))) ▷ (chains A X).X n = _
      exact MonoidalCategory.id_whiskerRight _ _
    rw [hz]
    simp only [Category.assoc, tensorInclusion_projection, Category.id_comp]
    change component A X n 0 n _ ≫ (vertexAugmentation A X ▷ (chains A X).X n) =
      (λ_ ((chains A X).X n)).inv ≫ 𝟙 ((𝟙_ (ModuleCat A)) ⊗ (chains A X).X n)
    rw [Category.comp_id]
    apply (cancel_mono (λ_ ((chains A X).X n)).hom).1
    simpa only [Category.assoc, Iso.inv_hom_id] using component_left_counit A X n
  · exact (Functor.map_isZero (tensorRight ((chains A X).X q))
      (isZero_single_obj_X (.down ℕ) 0 (𝟙_ (ModuleCat A)) p hp)).eq_of_tgt _ _

/-- 概要：AW 対角鎖写像の左余単位則（Berger–Fresse §1.1.4）。
方針：零次因子に射影し成分の左余単位則を適用する。
規約：単位の比較には既存の複体の左単位子を用いる。
使われ方：AW の余代数構造の左余単位則。 -/
lemma diagonal_left_counit (X : SSet.{0}) :
    diagonal A X ≫ HomologicalComplex.tensorHom (counit A X) (𝟙 (chains A X)) ≫
        (HomologicalComplex.leftUnitor (chains A X)).hom = 𝟙 _ := by
  rw [← Category.assoc, diagonal_counit_left_inv, Iso.inv_hom_id]

private lemma diagonal_counit_right_inv (X : SSet.{0}) :
    diagonal A X ≫ HomologicalComplex.tensorHom (𝟙 (chains A X)) (counit A X) =
      (HomologicalComplex.rightUnitor (chains A X)).inv := by
  apply HomologicalComplex.hom_ext
  intro n
  apply tensorProjection_hom_ext
  intro q p hpq
  by_cases hp : p = 0
  · subst p
    have hq : q = n := by omega
    subst q
    simp only [HomologicalComplex.comp_f, Category.assoc, tensorHom_projection,
      diagonal_projection_assoc, HomologicalComplex.id_f, MonoidalCategory.id_tensorHom,
      counit_f_zero]
    change component A X n n 0 _ ≫ ((chains A X).X n ◁ vertexAugmentation A X) =
      (HomologicalComplex.rightUnitor' (chains A X)).inv n ≫ _
    rw [HomologicalComplex.rightUnitor'_inv]
    have hz : (chains A X).X n ◁ (singleObjXSelf (.down ℕ) 0 (𝟙_ (ModuleCat A))).inv =
        𝟙 ((chains A X).X n ⊗ (𝟙_ (ModuleCat A))) := by
      change (chains A X).X n ◁ (𝟙 (𝟙_ (ModuleCat A))) = _
      exact MonoidalCategory.whiskerLeft_id _ _
    rw [hz]
    simp only [Category.assoc, tensorInclusion_projection, Category.id_comp]
    change component A X n n 0 _ ≫ ((chains A X).X n ◁ vertexAugmentation A X) =
      (ρ_ ((chains A X).X n)).inv ≫ 𝟙 ((chains A X).X n ⊗ (𝟙_ (ModuleCat A)))
    rw [Category.comp_id]
    apply (cancel_mono (ρ_ ((chains A X).X n)).hom).1
    simpa only [Category.assoc, Iso.inv_hom_id] using component_right_counit A X n
  · exact (Functor.map_isZero (tensorLeft ((chains A X).X q))
      (isZero_single_obj_X (.down ℕ) 0 (𝟙_ (ModuleCat A)) p hp)).eq_of_tgt _ _

/-- 概要：AW 対角鎖写像の右余単位則（Berger–Fresse §1.1.4）。
方針：零次因子に射影し成分の右余単位則を適用する。
規約：単位の比較には既存の複体の右単位子を用いる。
使われ方：AW の余代数構造の右余単位則。 -/
lemma diagonal_right_counit (X : SSet.{0}) :
    diagonal A X ≫ HomologicalComplex.tensorHom (𝟙 (chains A X)) (counit A X) ≫
        (HomologicalComplex.rightUnitor (chains A X)).hom = 𝟙 _ := by
  rw [← Category.assoc, diagonal_counit_right_inv, Iso.inv_hom_id]

/-- 概要：augmentation 鎖写像は単体集合の射に自然（Berger–Fresse §1.1.4）。
方針：single₀ への射を零次で比較し、全頂点が 1 に写ることを使う。
規約：任意の小さい単体集合の射に対する等式である。
使われ方：Hopf 余単位の同変性と自然性を供給する。 -/
lemma counit_natural {X Y : SSet.{0}} (f : X ⟶ Y) :
    chainMap A f ≫ counit A Y = counit A X := by
  apply (ChainComplex.toSingle₀Equiv _ _).injective
  apply Subtype.ext
  change (chainMap A f).f 0 ≫ (counit A Y).f 0 = (counit A X).f 0
  simp only [counit_f_zero]
  apply generator_hom_ext A X 0
  intro x
  simp

end SerrePositivity.EInfinity.AlexanderWhitney
