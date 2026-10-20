module
public import SerrePositivity.InfinityCategories.Derived.DGModuleOutputResolutionHomotopy
public import SerrePositivity.InfinityCategories.Derived.DGSemifreeDerivedHomInfinity
/-!
概要：固定入力ごとの D(R) 値 Hom の augmentation を、全単体上の自然な比較にする。
方針：実出力比較のホモトピーを元の半自由入力へ制限し、反変側は実反対 nerve を経由する。
規約：値域は全 R 加群の生の dg nerve。ここで準同型を可逆と主張しない。
使われ方：空間値 Hom との自然な比較に用いる、実 augmentation の関手族。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
/-- 同じ入力宇宙で扱う、全 dg R 加群の実 nerve。 -/
abbrev dgHomModuleNerve (_D : Type v) :=
  dgNerve R (DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
/-- 実 D(R) の半自由模型から、全 dg R 加群への実包含。 -/
def dgHomModuleInclusionInfinity : dgHomDerivedNerve R D ⟶ dgHomModuleNerve R D :=
  dgNerve.map (dgModuleOutputInclusionLift.{u, max (u + 1) v, 0} R PUnit.{1})
/-- 固定始域の、元の同じ全 Hom の実 R 加群値 ∞ 関手。 -/
def dgSemifreeHomTargetModuleInfinity (P : SemifreeDGModules R D) :
    dgModuleDerivedInfinityCategory R D ⟶ dgHomModuleNerve R D :=
  dgNerve.map ((dgSemifreeHomTargetModuleDG R D P).comp
    (dgUniverseLiftUp.{u, u + 1, max (u + 1) v} R (RightModule R PUnit.{1})))
/-- 固定終域の、dg 反対模型からの同じ全 Hom の実 R 加群値 ∞ 関手。 -/
def dgSemifreeHomSourceModuleInfinity (Q : SemifreeDGModules R D) :
    dgNerve R (SemifreeDGModules R D)ᵒᵖ ⟶ dgHomModuleNerve R D :=
  dgNerve.map ((dgSemifreeHomSourceModuleDG R D Q).comp
    (dgUniverseLiftUp.{u, u + 1, max (u + 1) v} R (RightModule R PUnit.{1})))
/-- 共変 D(R) 値 Hom の包含から元の Hom への、全単体上の実 augmentation。 -/
def dgSemifreeDerivedHomTargetAugmentationInfinity (P : SemifreeDGModules R D) :
    SSet.Homotopy (dgSemifreeDerivedHomTargetInfinity R D P ≫
      dgHomModuleInclusionInfinity R D) (dgSemifreeHomTargetModuleInfinity R D P) := by
  let H := functorHomotopyPrecomp
    (dgModuleOutputResolutionHomotopy R (SemifreeDGModules R D) PUnit.{1}
      (dgSemifreeHomTargetModuleDG R D P))
    (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, u + 1} R (SemifreeDGModules R D)))
  have h1 : dgNerve.map
      (dgUniverseLiftUp.{u, max (u + 1) v, u + 1} R (SemifreeDGModules R D)) ≫
        dgNerve.map (dgModuleOutputOriginalLift R (SemifreeDGModules R D) PUnit.{1}
          (dgSemifreeHomTargetModuleDG R D P)) =
      dgSemifreeHomTargetModuleInfinity R D P := by
    rw [← dgNerve.map_comp, dgModuleOutputOriginalLift_up]
    rfl
  exact { h := H.h
          h₀ := H.h₀.trans (Category.assoc _ _ _).symm
          h₁ := H.h₁.trans h1
          rel := H.rel }
/-- dg 反対模型上の D(R) 値 Hom から元の Hom への、全単体上の実 augmentation。 -/
def dgSemifreeDerivedHomSourceAugmentationInfinity (Q : SemifreeDGModules R D) :
    SSet.Homotopy (dgSemifreeDerivedHomSourceDGopInfinity R D Q ≫
      dgHomModuleInclusionInfinity R D) (dgSemifreeHomSourceModuleInfinity R D Q) := by
  let H := functorHomotopyPrecomp
    (dgModuleOutputResolutionHomotopy R (SemifreeDGModules R D)ᵒᵖ PUnit.{1}
      (dgSemifreeHomSourceModuleDG R D Q))
    (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, u + 1} R (SemifreeDGModules R D)ᵒᵖ))
  have h1 : dgNerve.map
      (dgUniverseLiftUp.{u, max (u + 1) v, u + 1} R (SemifreeDGModules R D)ᵒᵖ) ≫
        dgNerve.map (dgModuleOutputOriginalLift R (SemifreeDGModules R D)ᵒᵖ PUnit.{1}
          (dgSemifreeHomSourceModuleDG R D Q)) =
      dgSemifreeHomSourceModuleInfinity R D Q := by
    rw [← dgNerve.map_comp, dgModuleOutputOriginalLift_up]
    rfl
  exact { h := H.h
          h₀ := H.h₀.trans (Category.assoc _ _ _).symm
          h₁ := H.h₁.trans h1
          rel := H.rel }
/-- 実反対 ∞ 圏からの、元の同じ全 Hom の R 加群値 ∞ 関手。 -/
def dgSemifreeHomContravariantModuleInfinity (Q : SemifreeDGModules R D) :
    (dgModuleDerivedInfinityCategory R D).op ⟶ dgHomModuleNerve R D :=
  (dgNerveOppositeIso R (SemifreeDGModules R D)).hom ≫
    dgSemifreeHomSourceModuleInfinity R D Q
/-- 実反対 ∞ 圏上でも、同じ実 augmentation は全関手の間のホモトピー。 -/
def dgSemifreeDerivedHomContravariantAugmentationInfinity (Q : SemifreeDGModules R D) :
    SSet.Homotopy (dgSemifreeDerivedContravariantHomInfinity R D Q ≫
      dgHomModuleInclusionInfinity R D) (dgSemifreeHomContravariantModuleInfinity R D Q) := by
  let H := functorHomotopyPrecomp (dgSemifreeDerivedHomSourceAugmentationInfinity R D Q)
    (dgNerveOppositeIso R (SemifreeDGModules R D)).hom
  exact { h := H.h
          h₀ := H.h₀.trans (Category.assoc _ _ _).symm
          h₁ := H.h₁
          rel := H.rel }
end SerrePositivity.InfinityCategories
