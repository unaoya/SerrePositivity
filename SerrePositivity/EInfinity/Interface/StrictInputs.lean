module

public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import SerrePositivity.EInfinity.Interface.Core
public import SerrePositivity.HomologicalAlgebra.CochainDiscreteAlgebra

/-!
# 通常の代数の次数零 cdga

## 概要
HA §7.1.3 の離散入力のため、通常の可換代数を零次複体の可換モノイドに送る。

## 方針
元の代数の単位と乗法を加群で読み、零次埋め込みのモノイダル構造で移す。

## 規約
基底の作用と元の線形写像を使う。

## 使われ方
BS 著者版 Theorem 6.2 の形式の増大と、余単体的 cdga の比較。
-/

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded

namespace SerrePositivity.EInfinity

variable (S : Type u) [CommRing S]

private def discreteModuleMonoid (B : CommAlgCat.{u} S) : CommMon (ModuleCat.{u} S) := by
  let := moduleAlgebraMonObj (R := S) B
  have : IsCommMonObj (ModuleCat.of S B) := by
    refine ⟨?_⟩
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    exact LinearMap.ext fun x => LinearMap.ext fun y => mul_comm y x
  exact ⟨ModuleCat.of S B⟩

private def discreteModuleMonoidMap {B D : CommAlgCat.{u} S} (f : B ⟶ D) :
    discreteModuleMonoid S B ⟶ discreteModuleMonoid S D :=
  CommMon.homMk
    { hom := ModuleCat.ofHom f.hom.toLinearMap
      isMonHom_hom :=
        { one_hom := ModuleCat.hom_ext (LinearMap.ext fun r => f.hom.commutes r)
          mul_hom := by
            apply ModuleCat.hom_ext
            apply TensorProduct.ext
            exact LinearMap.ext fun x => LinearMap.ext fun y => f.hom.map_mul x y } }

private def discreteModuleMonoidFunctor : CommAlgCat.{u} S ⥤ CommMon (ModuleCat.{u} S) where
  obj := discreteModuleMonoid S
  map := discreteModuleMonoidMap S
  map_id _ := CommMon.hom_ext _ _ rfl
  map_comp _ _ := CommMon.hom_ext _ _ rfl

/-- 通常の代数を元の積を持つ次数零の可換 dg 代数として読む。 -/
@[no_expose] def discreteCDGA : RingAlgebra S ⥤ CommMon (Complex S) :=
  (commAlgCatEquivUnder (CommRingCat.of S)).inverse ⋙ discreteModuleMonoidFunctor S ⋙
    (CochainComplex.singleFunctor (ModuleCat S) 0).mapCommMon

end SerrePositivity.EInfinity
