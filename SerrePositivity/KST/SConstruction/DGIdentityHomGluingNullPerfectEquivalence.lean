module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingNullNativeEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveReflectsQuasiEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPretriangulatedQuasiEquivalenceForward
public import SerrePositivity.KST.SConstruction.DGKUniverseMorita
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGMoritaAction
public import SerrePositivity.KST.SConstruction.DGKPerfectNuEquivalence

/-!
概要：元恒等対角の V 因子化を、同じ固定 ν 辺の同値へ接続する。
方針：D 正本の nerve 準同値反映を元因子化へ適用し、元実 Perf 作用へ渡す。
規約：始域のみ前三角とし、V の前三角性や S 内の同値を仮定しない。
使われ方：共通長方形の実右面と絶対恒等面の頂点比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories LocalizingInvariants
variable (R : Type u) [CommRing R] (C : Type (u + 1)) [DGCategory R C] [Small.{u} C]
local notation "V" => DGIdentityHomGluingNullDomain R C
local notation "f" => dgIdentityHomGluingDiagonalNullFactor R C

/-- 概要：元対角の V 因子化は始域が前三角なら dg 準同値。
方針：元 native 指定同値を D 正本の全次数反映へ渡す。
規約：元 dg 関手を保持。使われ方：実 Perf 作用の Morita 同値。 -/
lemma dgIdentityHomGluingDiagonalNullFactor_quasiEquivalence
    [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C] : QuasiEquivalence (f) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_quasiEquivalence_of_nerve R C (V) (f)
    (dgIdentityHomGluingNullNativeEquivalence R C).isQCatEquivalence

/-- 概要：元 cone 可縮対象の V は始域の前三角性を受け継ぐ。
方針：同じ元対角因子化の準同値に D 正本の前三角性移送を適用する。
規約：新しい対象模型を選ばない。使われ方：V の元 Yoneda・ν 自然性。 -/
lemma dgIdentityHomGluingNullDomain_pretriangulated
    [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C] : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (V) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isDGPretriangulated_of_quasiEquivalence_forward R C (V) (f)
    (dgIdentityHomGluingDiagonalNullFactor_quasiEquivalence R C)

/-- 概要：元対角因子化を固定 S の同じ厳密辺として保持する。
方針：元全 Hom を共通対象宇宙へ持ち上げる。
規約：元対角の始域を変更しない。使われ方：実 V 頂点の ν 比較辺。 -/
def dgIdentityHomGluingDiagonalNullFactorInputMap :
    dgIdentityHomGluingBaseInput R C ⟶ dgIdentityHomGluingNullInput R C :=
  ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, u + 1, u + 1, u + 1, u + 1} (f))

/-- 概要：同じ固定 S 因子化辺の ν 像は実完全同値。
方針：元準同値の主 Perf 同値を宇宙持ち上げし、同じラベル作用へ渡す。
規約：同じ ν 辺の底関手を保持。使われ方：実右面の始域比較。 -/
lemma dgIdentityHomGluingDiagonalNullFactorInputMap_nu_equivalence
    [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C] : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
    (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgKInputStableValue R (dgIdentityHomGluingBaseInput R C))
      (dgKInputStableValue R (dgIdentityHomGluingNullInput R C)) from
      dgKInputNuMap R (dgIdentityHomGluingDiagonalNullFactorInputMap R C)).hom := by
  letI : (quasiEquivalencePerfectExtension R C (V) (f)).IsEquivalence :=
    (quasiEquivalencePerfectEquivalence R C (V) (f)
      (dgIdentityHomGluingDiagonalNullFactor_quasiEquivalence R C)).isEquivalence_functor
  letI : (quasiEquivalencePerfectExtension R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, u + 1} C)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, u + 1} (V))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, u + 1, u + 1, u + 1, u + 1} (f))).IsEquivalence :=
    dgKUniverseLiftFunctor_isMorita R C (V) (f)
  rw [dgKInputNuMap_eq]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGAction R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, u + 1} C) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, u + 1} (V))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, u + 1, u + 1, u + 1, u + 1} (f))))
  exact presentedPerfectDGMoritaAction_isQCatEquivalence R _ _ _

end SerrePositivity.KST.SConstruction
