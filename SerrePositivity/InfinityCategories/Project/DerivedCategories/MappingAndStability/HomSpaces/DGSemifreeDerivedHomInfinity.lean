module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Bar.DGModuleOutputResolutionAugmentation
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveOppositeIso
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
/-- 同じ入力宇宙で扱う、実半自由 R 加群の導来 nerve。 -/
abbrev dgHomDerivedNerve (_D : Type v) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R PUnit.{1}))
/-- 固定始域の同じ全 Hom 複体を、実 R 加群値の dg 関手へ送る。 -/
def dgSemifreeHomTargetModuleDG (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) (RightModule R PUnit.{1}) :=
  (_root_.SerrePositivity.DifferentialGraded.leftRepresentable R P).comp (_root_.SerrePositivity.DifferentialGraded.ringConstantDG R)
/-- 固定始域の全 Hom から作る、実 D(R) 値共変 ∞ 関手。 -/
def dgSemifreeDerivedHomTargetInfinity (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D ⟶ dgHomDerivedNerve R D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, u + 1} R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionInfinity R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) PUnit.{1}
      (dgSemifreeHomTargetModuleDG R D P)
/-- 固定終域の同じ全 Hom 複体を、実 R 加群値の反変 dg 関手へ送る。 -/
def dgSemifreeHomSourceModuleDG (Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ (RightModule R PUnit.{1}) :=
  (_root_.SerrePositivity.DifferentialGraded.representable R Q).toFunctor.comp (_root_.SerrePositivity.DifferentialGraded.ringConstantDG R)
/-- dg 反対模型からの、実 D(R) 値 Hom の ∞ 関手。 -/
def dgSemifreeDerivedHomSourceDGopInfinity (Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ ⟶ dgHomDerivedNerve R D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, u + 1} R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionInfinity R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ PUnit.{1}
      (dgSemifreeHomSourceModuleDG R D Q)
/-- 実反対 ∞ 圏からの、実 D(R) 値反変 Hom 関手。 -/
def dgSemifreeDerivedContravariantHomInfinity (Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D).op ⟶ dgHomDerivedNerve R D :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)).hom ≫
    dgSemifreeDerivedHomSourceDGopInfinity R D Q
end SerrePositivity.InfinityCategories.Project.DerivedCategories
