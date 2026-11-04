module

public import SerrePositivity.CommutativeAlgebra.EtaleStratification.FiniteFieldProduct
public import SerrePositivity.CommutativeAlgebra.UniversalHomeomorphism.NilDiagonal

/-!
# 一般点での純非分離部分の積

## 概要
有限個の有限純非分離体拡大の積の射は普遍同相。

## 方針
有限性と単射性から整性・Spec 全射性を得る。
体値点は一成分を経由し、冪等元で成分を特定した後に純非分離性による一意性を使う。

## 規約
積の射は成分ごとの構造射。

## 使われ方
一般点で取り出した分離部分の後半の射。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.CommutativeAlgebra

/-- 有限純非分離体拡大の有限積は普遍同相。 -/
theorem isUniversalHomeomorphism_pi_of_isPurelyInseparable
    {ι : Type u} [Finite ι] (M L : ι → Type u)
    [∀ i, Field (M i)] [∀ i, Field (L i)] [∀ i, Algebra (M i) (L i)]
    [∀ i, Module.Finite (M i) (L i)] [∀ i, IsPurelyInseparable (M i) (L i)] :
    IsUniversalHomeomorphism (RingHom.pi (fun i ↦
      (algebraMap (M i) (L i)).comp (Pi.evalRingHom M i))) := by
  classical
  let : ∀ i, Algebra (∀ j, M j) (M i) := fun i ↦ (Pi.evalRingHom M i).toAlgebra
  let : ∀ i, Algebra (∀ j, M j) (L i) := fun i ↦
    ((algebraMap (M i) (L i)).comp (Pi.evalRingHom M i)).toAlgebra
  let : ∀ i, IsScalarTower (∀ j, M j) (M i) (L i) := fun _ ↦
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : ∀ i, Module.Finite (∀ j, M j) (M i) := fun i ↦ (finite_etale_pi_component M i).1
  let : ∀ i, Module.Finite (∀ j, M j) (L i) := fun i ↦ Module.Finite.trans (M i) (L i)
  let F := RingHom.pi (fun i ↦ (algebraMap (M i) (L i)).comp (Pi.evalRingHom M i))
  let : Algebra (∀ i, M i) (∀ i, L i) := F.toAlgebra
  let : Module.Finite (∀ i, M i) (∀ i, L i) := inferInstance
  have hFint : F.IsIntegral := Algebra.IsIntegral.isIntegral
  have hFinj : Function.Injective F := by
    intro x y h
    funext i
    exact (algebraMap (M i) (L i)).injective (congrFun h i)
  apply isUniversalHomeomorphism_of_injective_fieldMaps F hFint (hFint.comap_surjective hFinj)
  intro K _ u v huv
  obtain ⟨i, a, ha⟩ := exists_field_factor L K u
  obtain ⟨j, b, hb⟩ := exists_field_factor L K v
  have hij : i = j := by
    by_contra hij
    have he := RingHom.congr_fun huv (Pi.single i (1 : M i))
    rw [← ha, ← hb] at he
    simpa [F, hij, hij.symm] using he
  subst j
  have hab : a.comp (algebraMap (M i) (L i)) = b.comp (algebraMap (M i) (L i)) := by
    ext x
    have he := RingHom.congr_fun huv (Pi.single i x)
    rw [← ha, ← hb] at he
    simpa [F] using he
  have he : a = b := IsPurelyInseparable.injective_comp_algebraMap (M i) (L i) K hab
  exact ha.symm.trans (he ▸ hb)

end SerrePositivity.CommutativeAlgebra
