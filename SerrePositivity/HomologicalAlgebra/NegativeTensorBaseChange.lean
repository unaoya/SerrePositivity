module
public import SerrePositivity.HomologicalAlgebra.MapExtendComplex
public import SerrePositivity.HomologicalAlgebra.CochainTensor.BaseChange
public import SerrePositivity.EInfinity.NegativeTensor.Comparison

/-!
概要：係数拡大した自然数鎖テンソルの負次数延長を、移した両因子のテンソルへ結ぶ。
方針：零延長の交換、負次数テンソル比較、既存 cochainTensorBaseChangeIso を合成する。
規約：各段の指定同型を保持し、平坦性や有界性を要求しない。
使われ方：HA 1.2.4、G10 の係数拡大後の EZ 比較のテンソル側。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory HomologicalComplex
namespace SerrePositivity.HomologicalAlgebra
variable {R A : Type u} [CommRing R] [CommRing A]
variable (φ : R →+* A) (K L : ChainComplex (ModuleCat.{u} R) ℕ)

/-- 移した自然数鎖テンソルを延長し、移した二因子の延長のテンソルへ比較する。 -/
def negativeTensorBaseChangeIso :
    (((ModuleCat.extendScalars φ).mapHomologicalComplex (.down ℕ)).obj
      (HomologicalComplex.tensorObj K L)).extend ComplexShape.embeddingDownNat ≅
    HomologicalComplex.tensorObj
      ((((ModuleCat.extendScalars φ).mapHomologicalComplex (.down ℕ)).obj K).extend
        ComplexShape.embeddingDownNat)
      ((((ModuleCat.extendScalars φ).mapHomologicalComplex (.down ℕ)).obj L).extend
        ComplexShape.embeddingDownNat) :=
  (mapExtendIso (ModuleCat.extendScalars φ) ComplexShape.embeddingDownNat
    (HomologicalComplex.tensorObj K L)).symm ≪≫
  ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).mapIso
    (EInfinity.NegativeTensor.comparison K L) ≪≫
  cochainTensorBaseChangeIso φ (K.extend ComplexShape.embeddingDownNat)
    (L.extend ComplexShape.embeddingDownNat) ≪≫
  tensorIso (mapExtendIso (ModuleCat.extendScalars φ) ComplexShape.embeddingDownNat K)
    (mapExtendIso (ModuleCat.extendScalars φ) ComplexShape.embeddingDownNat L)

end SerrePositivity.HomologicalAlgebra
