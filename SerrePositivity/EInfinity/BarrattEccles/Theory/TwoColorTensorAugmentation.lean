module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorTensorProjective
public import SerrePositivity.EInfinity.BarrattEccles.Theory.RepresentationChainAugmentation
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Symmetric
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Bounds

/-!
# 二色のテンソル係数の指定増大

## 概要
HA 3.2.4.7 の二色比較に使う、実際の二つの arity のテンソルの増大を構成する。

## 方針
既存の二つの増大と単位子を合成し、同じ二つの収縮のテンソルで擬同型性を証明する。

## 規約
群同変な収縮は要求せず、指定増大だけを表現の圏へ移す。

## 使われ方
二色比較の終域の射影解像度と増大の可換性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 二つの実際の収縮のテンソルと、零次単位の左単位子との合成。 -/
def twoColorTensorContraction (m n : ℕ) :
    HomotopyEquiv (complex A m ⊗ complex A n) (complexSphere A 0) :=
  (cochainTensorHomotopyEquiv (complexContraction A m) (complexContraction A n)).trans
    (HomotopyEquiv.ofIso (λ_ (complexSphere A 0)))

/-- 実際の二色テンソル係数の指定された増大。 -/
def twoColorTensorAugmentation (m n : ℕ) :
    complex A m ⊗ complex A n ⟶ complexSphere A 0 :=
  (twoColorTensorContraction A m n).hom

/-- 指定増大は、二つの元の増大のテンソルと単位子そのもの。 -/
lemma twoColorTensorAugmentation_eq (m n : ℕ) :
    twoColorTensorAugmentation A m n =
      (complexAugmentation A m ⊗ₘ complexAugmentation A n) ≫
        (λ_ (complexSphere A 0)).hom := rfl

/-- 指定されたテンソル増大は二色部分群の作用に関して不変。 -/
lemma twoColorTensorAugmentation_invariant (m n : ℕ) (g : TwoColorGroup.{u} m n) :
    (tensorComplexAction (twoColorLeftAction A m n) (twoColorRightAction A m n) g).asHom ≫
      twoColorTensorAugmentation A m n = twoColorTensorAugmentation A m n := by
  rw [twoColorTensorAugmentation_eq]
  change ((complexRightAction A m (twoColorLeftProjection m n g).down⁻¹) ⊗ₘ
    (complexRightAction A n (twoColorRightProjection m n g).down⁻¹)) ≫
    (complexAugmentation A m ⊗ₘ complexAugmentation A n) ≫ _ = _
  rw [← Category.assoc, tensorHom_comp_tensorHom,
    complexRightAction_augmentation, complexRightAction_augmentation]

/-- テンソル係数の正一次は零であり、制限した収縮の境界項が消える。 -/
lemma twoColorTensor_isZero_one (m n : ℕ) :
    IsZero ((complex A m ⊗ complex A n).X 1) := by
  apply cochainTensor_isZero_X_of_summands
  intro i j hij
  by_cases hi : 0 < i
  · exact Or.inl (complex_isZero_positive A m i hi)
  · exact Or.inr (complex_isZero_positive A n j (by omega))

/-- 群作用を忘れた収縮を、その指定順射のまま鎖次数へ移す。 -/
def twoColorTensorRestrictionContraction (m n : ℕ) :
    HomotopyEquiv ((complex A m ⊗ complex A n).restriction ComplexShape.embeddingDownNat)
      ((complexSphere A 0).restriction ComplexShape.embeddingDownNat) :=
  nonpositiveHomotopyEquivRestriction (twoColorTensorContraction A m n)
    (twoColorTensor_isZero_one A m n)
    (isZero_single_obj_X (.up ℤ) 0 (𝟙_ (ModuleCat A)) 1 (by decide))

/-- 元の指定増大の制限は、任意の可換環上で擬同型である。 -/
lemma twoColorTensorAugmentationRestriction_quasiIso (m n : ℕ) :
    QuasiIso (restrictionMap (twoColorTensorAugmentation A m n)
      ComplexShape.embeddingDownNat) :=
  HomotopyEquiv.quasiIso_hom (twoColorTensorRestrictionContraction A m n)

/-- 実際の二色テンソル係数を表現の圏の鎖複体として読む。 -/
def twoColorTensorChain (m n : ℕ) : ChainComplex (Rep.{u} A (TwoColorGroup.{u} m n)) ℕ :=
  (representationCochainComplex
    (tensorComplexAction (twoColorLeftAction A m n) (twoColorRightAction A m n))).restriction
      ComplexShape.embeddingDownNat

/-- テンソル係数の指定増大を、表現の圏の鎖複体の増大として読む。 -/
def twoColorTensorChainAugmentation (m n : ℕ) :
    twoColorTensorChain A m n ⟶
      (ChainComplex.single₀ (Rep.{u} A (TwoColorGroup.{u} m n))).obj
        (Rep.trivial A (TwoColorGroup.{u} m n) (𝟙_ (ModuleCat A))) :=
  representationChainAugmentation
    (tensorComplexAction (twoColorLeftAction A m n) (twoColorRightAction A m n))
    (𝟙_ (ModuleCat A)) (twoColorTensorAugmentation A m n)
    (twoColorTensorAugmentation_invariant A m n)

/-- 表現の圏の指定されたテンソル増大は擬同型。 -/
lemma twoColorTensorChainAugmentation_quasiIso (m n : ℕ) :
    QuasiIso (twoColorTensorChainAugmentation A m n) := by
  have := twoColorTensorAugmentationRestriction_quasiIso A m n
  exact representationChainAugmentation_quasiIso _ _ _ _

/-- 実際のテンソル係数と指定増大からなる終域の射影解像度。 -/
def twoColorTargetResolution (m n : ℕ) :
    ProjectiveResolution (Rep.trivial A (TwoColorGroup.{u} m n) (𝟙_ (ModuleCat A))) where
  complex := twoColorTensorChain A m n
  projective q := twoColorTensorDegree_projective A m n (-(q : ℤ))
  π := twoColorTensorChainAugmentation A m n
  quasiIso := twoColorTensorChainAugmentation_quasiIso A m n

end SerrePositivity.EInfinity.BarrattEccles
