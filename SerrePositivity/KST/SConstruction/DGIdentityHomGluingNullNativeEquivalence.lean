module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingNullNativeComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGFunctors.DGFunctorFullyFaithful

/-!
概要：元恒等対角の始域と V の native nerve の指定同値を作る。
方針：元対角因子化・元左射影と保存済み全比較を充満包含で反映する。
規約：固定 S の strict Hom end 同値や dg 準同値とは区別する。
使われ方：実 V 零化面の頂点を元恒等対角始域へ指定比較する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type (u + 1)) [DGCategory R C] [Small.{u} C]
local notation "I" => DGFunctor.id C
local notation "M" => dgHomGluingBimodule R C C C (I) (I)
local notation "L" => DGIdentityHomGluing R C
local notation "V" => DGIdentityHomGluingNullDomain R C
local notation "j" => dgIdentityHomGluingNullInclusion R C
local notation "f" => dgIdentityHomGluingDiagonalNullFactor R C
local notation "p" => dgIdentityHomGluingNullProjection R C

/-- 概要：元対角因子化の後の V 射影は元恒等 dg 関手。
方針：元包含回収と strict 対角の左射影則を使用する。
規約：全関手の厳密等号。使われ方：指定同値の始域側単位。 -/
lemma dgIdentityHomGluingDiagonalNullFactor_projection : (f).comp (p) = DGFunctor.id C := by
  rw [dgIdentityHomGluingNullProjection, ← strictDGFunctor_comp_assoc,
    dgIdentityHomGluingDiagonalNullFactor_inclusion]
  exact dgStrictSquareDiagonal_left R C C C (I) (I) (I) (I) rfl

/-- 概要：元対角因子化と V 射影の native nerve は互いに指定逆。
方針：片側は元厳密等号、他側は元全比較を同じ充満包含で反映する。
規約：同じ二 dg 関手を順逆に保持。使われ方：元 V 頂点の native 回収。 -/
def dgIdentityHomGluingNullNativeEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (V)) := by
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (f)
  let P := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (p)
  let J := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (j)
  have hj : F ≫ J = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgIdentityHomGluingDiagonal R C) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp _ _).symm.trans
      (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgIdentityHomGluingDiagonalNullFactor_inclusion R C))
  have hf : F ≫ P = 𝟙 _ :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp _ _).symm.trans
      ((congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgIdentityHomGluingDiagonalNullFactor_projection R C)).trans
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_id)
  have e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (V))) ≫ J) ((P ≫ F) ≫ J) := by
    exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (dgIdentityHomGluingNullNativeComparison R C)
      (Category.id_comp J).symm
      (by rw [Category.assoc, hj])
  have hJ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful J :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSubcategoryInclusionNerve_isFullyFaithful R (L) (dgIdentityHomGluingNullProperty R C)
  exact ⟨F, P, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
    (Iso.refl (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C))))) hf.symm rfl,
    (hJ.preimageFunctorIso e).symm⟩

end SerrePositivity.KST.SConstruction
