module

public import SerrePositivity.BhattScholze.Prism.Bounded.CompleteFlatDiscrete
import all SerrePositivity.BhattScholze.Prism.Bounded.CompleteFlatReduction
import all SerrePositivity.BhattScholze.Prism.Bounded.CompletelyFlatPrism
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerTorsionTor
import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeRightTensor
import SerrePositivity.HomologicalAlgebra.DerivedRestrictionConservative
import SerrePositivity.HomologicalAlgebra.ScalarExtensionTensorTests

/-!
# 完備底変換の導来完全平坦性

## 概要
二元イデアルに関する完全平坦性は、そのイデアルに沿う完備底変換で保たれる。

## 方針
通常の導来底変換の剰余を係数制限で調べ、完備化の単位が冪ねじれの試験対象では同型になることを使う。

## 規約
BS 著者版 Corollary 3.12 (a) の完全平坦性の導来計算。

## 使われ方
有界 prism の忠実平坦な押し出し。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace SerrePositivity.BhattScholze.Prismatic

open CategoryTheory CategoryTheory.Limits DerivedCompletion MonoidalCategory HomologicalComplex
attribute [local instance] HasDerivedCategory.standard

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

private theorem completion_reduction_unit_isIso
    (q : B →+* C) (a : B) (ha : q a = 0) (X : DerivedCategory.Minus (ModuleCat.{u} B)) :
    IsIso ((boundedAboveDerivedBaseChange q).map ((boundedAboveDerivedCompletionUnit B a).app X)) := by
  let N := baseChangeScalarModule q
  have hN : ∀ x : N, a ^ (1 : ℕ) • x = 0 := by
    intro x
    rw [pow_one]
    change q a * (show C from x) = 0
    rw [ha, zero_mul]
  let u := (boundedAboveDerivedCompletionUnit B a).app X
  have ht := completionUnit_tensor_module_powerTorsion_isIso B a X N 1 hN
  let : IsIso ((boundedAboveDerivedRestrictScalars q).map ((boundedAboveDerivedBaseChange q).map u)) :=
    (NatIso.isIso_map_iff (boundedAboveDerivedBaseChangeRightTensorNatIso q) u).mpr ht
  exact isIso_of_reflects_iso ((boundedAboveDerivedBaseChange q).map u)
    (boundedAboveDerivedRestrictScalars q)

variable [Algebra A C]

/-- 上に有界な対象の、二元で完備化した底変換。 -/
abbrev pairCompletedBaseChange (g : A →+* B) (a b : B)
    (X : DerivedCategory.Minus (ModuleCat.{u} A)) :
    DerivedCategory.Minus (ModuleCat.{u} B) :=
  (boundedAboveDerivedCompletionFunctor B b).obj
    ((boundedAboveDerivedCompletionFunctor B a).obj ((boundedAboveDerivedBaseChange g).obj X))

/-- 概要：完全平坦な加群の二座標完備底変換は、底変換した二座標について完全平坦。
方針：通常の係数拡大を、剰余で零化される試験加群とのテンソルで調べる。
規約：BS 著者版 Corollary 3.12 (a) の完全平坦な押し出しの導来部分。
使われ方：完備テンソル積の零次で完全平坦性を得る。 -/
theorem pairCompletedBaseChange_completelyFlat (g : A →+* B) (I : Ideal A) (a b : B)
    (hg : I.map g = Ideal.span {a, b}) (hf : IsCompletelyFlat I C) :
    IsDerivedCompletelyFlat (Ideal.span {a, b})
      (pairCompletedBaseChange g a b (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A C))) := by
  let X := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A C)
  let Y := (boundedAboveDerivedBaseChange g).obj X
  let Z := (boundedAboveDerivedCompletionFunctor B a).obj Y
  let J := Ideal.span {a, b}
  let q := Ideal.Quotient.mk J
  let t := q.comp g
  have hflat := discrete_completelyFlat I (ModuleCat.of A C) hf
  unfold IsDerivedCompletelyFlat at hflat
  have ht : I ≤ RingHom.ker t := by
    intro r hr
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change g r ∈ Ideal.span {a, b}
    rw [← hg]
    exact Ideal.mem_map_of_mem g hr
  have htest (N : ModuleCat.{u} (B ⧸ J)) (i : ℤ) (hi : i ≠ 0) :=
    modelTensor_homology_isZero_of_flat_reduction I X hflat.1 hflat.2
      ((ModuleCat.restrictScalars t).obj N) (fun r hr x ↦ by
        change t r • (show N from x) = 0
        rw [show t r = 0 from ht hr, zero_smul]) i hi
  have hraw := derivedBaseChange_pure_flat_of_tensor_tests t X htest
  have hqa : q a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _))
  have hqb : q b = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
  have ha := completion_reduction_unit_isIso q a hqa Y
  have hb := completion_reduction_unit_isIso q b hqb Z
  let e := (DerivedCategory.Minus.ι.mapIso
      (asIso ((boundedAboveDerivedBaseChange q).map ((boundedAboveDerivedCompletionUnit B b).app Z)))).symm ≪≫
    (DerivedCategory.Minus.ι.mapIso
      (asIso ((boundedAboveDerivedBaseChange q).map ((boundedAboveDerivedCompletionUnit B a).app Y)))).symm ≪≫
    baseChangeCompositeIso g q X
  unfold IsDerivedCompletelyFlat
  refine ⟨fun i hi ↦ ?_, ?_⟩
  · apply IsZero.of_iso _ ((DerivedCategory.homologyFunctor (ModuleCat (B ⧸ J)) i).mapIso e)
    rcases lt_or_gt_of_ne hi with hi | hi
    · let := hraw.1
      exact DerivedCategory.isZero_of_isGE _ 0 i hi
    · let := hraw.2.1
      exact DerivedCategory.isZero_of_isLE _ 0 i hi
  · let := hraw.2.2
    exact Module.Flat.of_linearEquiv
      ((DerivedCategory.homologyFunctor (ModuleCat (B ⧸ J)) 0).mapIso e).toLinearEquiv

end SerrePositivity.BhattScholze.Prismatic
