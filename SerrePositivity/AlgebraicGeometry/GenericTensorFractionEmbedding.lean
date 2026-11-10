module

public import SerrePositivity.AlgebraicGeometry.FractionFieldLocalizationComparison
public import Mathlib.RingTheory.Flat.Basic

/-!
概要：平坦なアフィン環の生成ファイバーの関数体は、元の環の関数体でもある。
方針：生成ファイバーへの単射を平坦性から得て、局所化の分数表示の分母を払う。
規約：関数体は単射な代数準同型と分数表示で与える。
使われ方：降ろした超曲面模型と元の滑らかな族の共通分数体。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct nonZeroDivisors

/--
概要：平坦な代数の生成テンソル積が体に埋まり、その分数で体が尽くされれば、元の代数にも同じ分数表示がある。
方針：生成テンソル積を基底の非零因子の局所化とみなし、分数体を局所化の前に戻す。
規約：基底は整域、生成テンソル積は分数体を左に取る。
使われ方：共通分数体から超曲面模型と元のアフィン環の共通の主開を得る。
-/
theorem exists_fraction_embedding_of_genericTensor
    {A B K L : Type*} [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    (j : K ⊗[A] B →ₐ[K] L) (hj : Function.Injective j)
    (hFrac : ∀ z : L, ∃ x y, z = j x / j y) :
    ∃ (f : B →ₐ[A] L), Function.Injective f ∧ ∀ z : L, ∃ x y, z = f x / f y := by
  let T := K ⊗[A] B
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let i : B →ₐ[A] T := Algebra.TensorProduct.includeRight
  let f := (j.restrictScalars A).comp i
  have hi : Function.Injective i :=
    Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective A K)
  have hf : Function.Injective f := hj.comp hi
  let : Algebra B L := f.toRingHom.toAlgebra
  let : Algebra T L := j.toRingHom.toAlgebra
  let : IsScalarTower B T L := IsScalarTower.of_algebraMap_eq' rfl
  let : FaithfulSMul B L := (faithfulSMul_iff_algebraMap_injective B L).mpr hf
  let : FaithfulSMul T L := (faithfulSMul_iff_algebraMap_injective T L).mpr hj
  let : IsFractionRing T L := by
    apply IsFractionRing.of_field
    exact hFrac
  let M := Algebra.algebraMapSubmonoid B A⁰
  let : IsLocalization M T := by
    dsimp [M, T]
    infer_instance
  let : IsFractionRing B L := isFractionRing_of_isFractionRing_localization (S := T) M
  refine ⟨f, hf, fun z => ?_⟩
  obtain ⟨x, y, _, h⟩ := IsFractionRing.div_surjective B z
  exact ⟨x, y, h.symm⟩

end SerrePositivity.AlgebraicGeometry
