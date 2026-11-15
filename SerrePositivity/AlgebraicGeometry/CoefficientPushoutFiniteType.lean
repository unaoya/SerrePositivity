module

public import SerrePositivity.AlgebraicGeometry.CoefficientPushoutDiagram

/-!
概要：有限型の係数環の塔に沿って、pushout 模型の両辺の有限型性を保つ。
方針：有限生成係数部分代数と第一挿入の有限型性を合成する。
規約：両辺の k 構造は、同じ κ と実際の構造射の合成。
使われ方：B03・B04 の後段の模型を有限型 k-代数として登録する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
universe u
variable (A R S : Type u) [CommRing A] [CommRing R] [CommRing S]
  [Algebra A R] [Algebra A S] [Algebra.FiniteType A S]

/-- 固定した係数環から各 pushout への実際の構造射は有限型。 -/
theorem coefficientPushoutRootMap_finiteType (j : Finset R) :
    ((coefficientPushoutRootMap A R S).app j).hom.FiniteType := by
  change (((coefficientPushoutBaseMap A R S).app j).hom.comp
    (algebraMap A ((coefficientSubalgebraDiagram A R).obj j))).FiniteType
  exact (coefficientPushoutBaseMap_finiteType A R S j).comp
    (RingHom.finiteType_algebraMap.mpr inferInstance)

/-- 有限型な係数写像の後でも、両辺の実際の構造射は有限型。 -/
theorem coefficientPushout_base_source_finiteType
    {k : Type u} [CommRing k] (κ : k →+* A) (hκ : κ.FiniteType) (j : Finset R) :
    (((coefficientSubalgebraBaseNatTrans A R).app j).hom.comp κ).FiniteType ∧
      (((coefficientPushoutRootMap A R S).app j).hom.comp κ).FiniteType := by
  constructor
  · exact (RingHom.finiteType_algebraMap.mpr
      (inferInstance : Algebra.FiniteType A ((coefficientSubalgebraDiagram A R).obj j))).comp hκ
  · exact (coefficientPushoutRootMap_finiteType A R S j).comp hκ

end SerrePositivity.AlgebraicGeometry
