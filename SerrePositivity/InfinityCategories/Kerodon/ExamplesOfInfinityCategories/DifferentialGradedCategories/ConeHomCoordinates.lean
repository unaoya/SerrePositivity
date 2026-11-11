module
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-! # mapping cone への Hom の全次数座標

概要：mapping cone への斉次 cochain は二つの射影後の成分と線形に同値。
方針：Mathlib の fst・snd と liftCochain を互いに逆として使う。
規約：HA Construction 1.3.1.6、HTT §1.2.13。使われ方：N7c の Hom-fiber の厳密な比較。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded CochainComplex HomComplex

variable {A : Type u} [CommRing A] {X B D : Complex A}

/-- 概要：mapping cone への次数 n の cochain と二つの射影成分の A 線形同値。
方針：順写像は fst・snd との合成、逆写像は liftCochain、両逆則は射影の式と外延性。
規約：HTT §1.2.13、次数は fst が +1、snd が零。使われ方：Hom-fiber の全次数座標。 -/
def coneHomCoordinates (f : B ⟶ D) (n : ℤ) :
    Cochain X (mappingCone f) n ≃ₗ[A] (Cochain X B (n + 1) × Cochain X D n) where
  toFun a := (a.comp (mappingCone.fst f).val rfl, a.comp (mappingCone.snd f) (add_zero n))
  invFun a := mappingCone.liftCochain f a.1 a.2 rfl
  left_inv a := by
    apply (mappingCone.ext_cochain_to_iff f n (n + 1) rfl).2
    constructor
    · exact mappingCone.liftCochain_fst _ _ _ _
    · exact mappingCone.liftCochain_snd _ _ _ _
  right_inv a := by
    apply Prod.ext
    · exact mappingCone.liftCochain_fst _ _ _ _
    · exact mappingCone.liftCochain_snd _ _ _ _
  map_add' a b := by
    apply Prod.ext
    · exact Cochain.add_comp _ _ _ rfl
    · exact Cochain.add_comp _ _ _ (add_zero n)
  map_smul' c a := by
    apply Prod.ext
    · exact Cochain.smul_comp _ _ _ rfl
    · exact Cochain.smul_comp _ _ _ (add_zero n)

/-- 概要：cone Hom の第一座標は次数 +1 の射影との合成。
方針：線形同値の順写像の第一成分を評価する。
規約：HTT §1.2.13。使われ方：fiber の最初の二脚の計算。 -/
lemma coneHomCoordinates_fst (f : B ⟶ D) (n : ℤ) (a : Cochain X (mappingCone f) n) :
    (coneHomCoordinates f n a).1 = a.comp (mappingCone.fst f).val rfl := rfl

/-- 概要：cone Hom の第二座標は次数零の射影との合成。
方針：線形同値の順写像の第二成分を評価する。
規約：HTT §1.2.13。使われ方：fiber のホモトピー成分の計算。 -/
lemma coneHomCoordinates_snd (f : B ⟶ D) (n : ℤ) (a : Cochain X (mappingCone f) n) :
    (coneHomCoordinates f n a).2 = a.comp (mappingCone.snd f) (add_zero n) := rfl

/-- 概要：cone Hom の逆座標写像は Mathlib の liftCochain。
方針：線形同値の逆写像を評価する。
規約：HTT §1.2.13。使われ方：fiber の全次数の明示解。 -/
lemma coneHomCoordinates_symm (f : B ⟶ D) (n : ℤ)
    (a : Cochain X B (n + 1) × Cochain X D n) :
    (coneHomCoordinates f n).symm a = mappingCone.liftCochain f a.1 a.2 rfl := rfl

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
