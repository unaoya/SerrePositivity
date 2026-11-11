module
public import SerrePositivity.KST.SConstruction.DGGluingRightAxisHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseNerveFullyFaithful

/-! # 実右軸包含の dg nerve の充満忠実性
概要：元の右軸包含は、共通宇宙の dg nerve の実写像空間上で充満忠実となる。
方針：元の全 Hom 鎖同型をそのまま既存の nerve 判定へ適用する。
規約：h 圏だけの充満忠実性で代用しない。使われ方：商の右脚と生成元の比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (z : C) (hz : CategoryTheory.Limits.IsZero (ForgetEnrichment.of (Complex R) z))

/-- 元の実右軸包含は、共通宇宙で元の dg nerve の実写像空間上で充満忠実。 -/
lemma dgGluingRightAxis_nerve_fullyFaithful :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveUniverseMap (dgGluingRightAxis R C D M z hz)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveUniverseMap_isFullyFaithful_of_homIso _
    (dgGluingRightAxis_map_isIso R C D M z hz)

end SerrePositivity.KST.SConstruction
