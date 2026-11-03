module
public import SerrePositivity.InfinityCategories.Derived.DGModuleOutputResolutionAugmentation
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
public import SerrePositivity.InfinityCategories.Derived.DGNerveOppositeIso
/-!
概要：半自由 dg 加群の全 Hom 複体を、半自由 R 加群値の実共変・反変 ∞ 関手へ移す。
方針：実 Hom end を R 加群へ送り、厳密切断による実出力分解を全単体上で適用する。
規約：対象ごとの分解選択だけではない。値の実 augmentation は別途照合する。
使われ方：β5 の D(R) 値導来 Hom。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
/-- 同じ入力宇宙で扱う、実半自由 R 加群の導来 nerve。 -/
abbrev dgHomDerivedNerve (_D : Type v) :=
  dgNerve R (DGUniverseLift.{u + 1, max (u + 1) v} (SemifreeDGModules R PUnit.{1}))
/-- 固定始域の同じ全 Hom 複体を、実 R 加群値の dg 関手へ送る。 -/
def dgSemifreeHomTargetModuleDG (P : SemifreeDGModules R D) :
    DGFunctor R (SemifreeDGModules R D) (RightModule R PUnit.{1}) :=
  (leftRepresentable R P).comp (ringConstantDG R)
/-- 固定始域の全 Hom から作る、実 D(R) 値共変 ∞ 関手。 -/
def dgSemifreeDerivedHomTargetInfinity (P : SemifreeDGModules R D) :
    dgModuleDerivedInfinityCategory R D ⟶ dgHomDerivedNerve R D :=
  dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, u + 1} R (SemifreeDGModules R D)) ≫
    dgModuleOutputResolutionInfinity R (SemifreeDGModules R D) PUnit.{1}
      (dgSemifreeHomTargetModuleDG R D P)
/-- 固定終域の同じ全 Hom 複体を、実 R 加群値の反変 dg 関手へ送る。 -/
def dgSemifreeHomSourceModuleDG (Q : SemifreeDGModules R D) :
    DGFunctor R (SemifreeDGModules R D)ᵒᵖ (RightModule R PUnit.{1}) :=
  (representable R Q).toFunctor.comp (ringConstantDG R)
/-- dg 反対模型からの、実 D(R) 値 Hom の ∞ 関手。 -/
def dgSemifreeDerivedHomSourceDGopInfinity (Q : SemifreeDGModules R D) :
    dgNerve R (SemifreeDGModules R D)ᵒᵖ ⟶ dgHomDerivedNerve R D :=
  dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, u + 1} R (SemifreeDGModules R D)ᵒᵖ) ≫
    dgModuleOutputResolutionInfinity R (SemifreeDGModules R D)ᵒᵖ PUnit.{1}
      (dgSemifreeHomSourceModuleDG R D Q)
/-- 実反対 ∞ 圏からの、実 D(R) 値反変 Hom 関手。 -/
def dgSemifreeDerivedContravariantHomInfinity (Q : SemifreeDGModules R D) :
    (dgModuleDerivedInfinityCategory R D).op ⟶ dgHomDerivedNerve R D :=
  (dgNerveOppositeIso R (SemifreeDGModules R D)).hom ≫
    dgSemifreeDerivedHomSourceDGopInfinity R D Q
end SerrePositivity.InfinityCategories
