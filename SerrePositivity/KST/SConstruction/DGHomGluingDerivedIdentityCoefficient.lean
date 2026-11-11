module
public import SerrePositivity.KST.SConstruction.DGHomGluingIdentityCoefficient
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.LaxComparisonEquivalence

/-!
概要：恒等 Hom gluing の導来係数を元の導来 Yoneda に全単体で同定する。
方針：全 dg 関手等号を既存の共通宇宙 nerve と導来比較へ適用する。
規約：導来加群圏を基底とする比較であり、元基底の恒等 lax 圏との同定ではない。
使われ方：D2 の恒等 lax 全比較に必要な係数の同定を追加仮定なしで供給する。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
local notation "M" => dgHomGluingBimodule R C C C (DGFunctor.id C) (DGFunctor.id C)

/-- 概要：恒等 Hom gluing の実導来係数は元の導来 Yoneda と等しい。
方針：全 dg 係数等号を元の nerve と導来比較へ運ぶ。
規約：全単体での厳密等号。使われ方：同じ Yoneda 二脚への比較先の照合。 -/
lemma dgHomGluingUniverseDerivedIdentityCoefficient :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient.{u, v, v} R C C (M) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, v, v} R C := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseCoefficient _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseYoneda
  rw [dgHomGluingIdentity_coefficient]

/-- 概要：恒等 Hom gluing は同じ導来 Yoneda 二脚の実 lax pullback と同値。
方針：D2 の既存全比較に係数の厳密等号を代入する。
規約：元基底の恒等二脚への全比較は残る。使われ方：D2 接続の実中間比較。 -/
def dgHomGluingUniverseDerivedIdentityLaxEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    ((SSet.uliftFunctor.{max (u + 1) v, max u v}).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C C (M))))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, v, v} R C)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, v, v} R C)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxEquivalence R C C (M)
  rw [dgHomGluingUniverseDerivedIdentityCoefficient] at h
  exact h
end SerrePositivity.KST.SConstruction
