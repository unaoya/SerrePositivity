module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.UnitInputShuffle
public import SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorStandardInclusion
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorPowerSeparationAppend

/-!
# 指定 Hopf 入力の標準語での分離

HA 3.2.4.7 の自由比較の入力を、左右の指定単位族へ分離する（BS-W16 L13）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory MonoidalCategory Limits
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.freeAlgebra
variable (R : Type u) [CommRing R] (X Y : Complex R)

/-- 左の生成元の後ろに指定単位入力を置く、L13 の式 eL。 -/
def freeLeftUnitExtension (m n : ℕ) :
    power X m ⟶ power ((operad R).freeAlgebra X).carrier (m + n) :=
  (ρ_ (power X m)).inv ≫
    (TensorPowers.map ((operad R).schurUnit X) m ⊗ₘ
      nullaryUnitPower R ((operad R).freeAlgebra X) n) ≫
    (appendIso ((operad R).freeAlgebra X).carrier m n).hom

/-- 右の生成元の前に指定単位入力を置く、L13 の式 eR。 -/
def freeRightUnitExtension (m n : ℕ) :
    power Y n ⟶ power ((operad R).freeAlgebra Y).carrier (m + n) :=
  (λ_ (power Y n)).inv ≫
    (nullaryUnitPower R ((operad R).freeAlgebra Y) m ⊗ₘ
      TensorPowers.map ((operad R).schurUnit Y) n) ≫
    (appendIso ((operad R).freeAlgebra Y).carrier m n).hom

/-- 指定 Hopf 入力のテンソル冪は、同じ左右の単位入力の族へ分離される。 -/
lemma freeHopfComparisonInput_standard_separation (m n : ℕ)
    (h0 : IsIso ((hopf R).counit.map.app (FiniteBijection.of 0))) :
    (binaryTensorStandardPowersIso X Y m n).inv ≫
      binaryTensorWordInclusion X Y (m + n) (binaryTensorStandardPattern m n) ≫
      TensorPowers.map (freeHopfComparisonInput (hopf R) h0 X Y) (m + n) ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation ((operad R).freeAlgebra X).carrier
        ((operad R).freeAlgebra Y).carrier (m + n)).hom =
    freeLeftUnitExtension R X m n ⊗ₘ freeRightUnitExtension R Y m n := by
  rw [binaryTensorStandardPowersIso_inclusion]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← reassoc_of% (appendIso_naturality
    (freeHopfComparisonInput (hopf R) h0 X Y) m n), tensorHom_comp_tensorHom_assoc,
    ← TensorPowers.map_comp, ← TensorPowers.map_comp]
  simp only [freeHopfComparisonInput, biprod.inl_desc, biprod.inr_desc]
  change ((TensorPowers.map (((operad R).schurUnit X) ≫
    (ρ_ ((operad R).freeAlgebra X).carrier).inv ≫
      (𝟙 _ ⊗ₘ (hopfTensorUnitMap (hopf R) h0 ((operad R).freeAlgebra Y)).hom)) m) ⊗ₘ
    TensorPowers.map (((operad R).schurUnit Y) ≫
    (λ_ ((operad R).freeAlgebra Y).carrier).inv ≫
      ((hopfTensorUnitMap (hopf R) h0 ((operad R).freeAlgebra X)).hom ⊗ₘ 𝟙 _)) n) ≫
    (appendIso _ m n).hom ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation _ _ (m + n)).hom = _
  erw [rightUnitor_inv_naturality_assoc ((operad R).schurUnit X),
    whiskerRight_comp_tensorHom,
    leftUnitor_inv_naturality_assoc ((operad R).schurUnit Y), whiskerLeft_comp_tensorHom]
  erw [Category.comp_id, Category.comp_id]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation_append, tensorHom_comp_tensorHom_assoc,
    tensorPowerSeparation_insert_right, tensorPowerSeparation_insert_left]
  rw [reassoc_of% tensorμ_unit_insert]
  simp only [freeLeftUnitExtension, freeRightUnitExtension,
    nullaryUnitPower_eq R _ _ h0, tensorHom_comp_tensorHom, Category.assoc]

end SerrePositivity.EInfinity.BarrattEccles
