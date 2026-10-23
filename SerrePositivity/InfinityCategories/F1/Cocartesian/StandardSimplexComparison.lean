module

public import SerrePositivity.InfinityCategories.F1.Simplicial.SimplexNerveOver
public import SerrePositivity.InfinityCategories.F1.Cocartesian.FiniteSimplexEquivalence
public import SerrePositivity.InfinityCategories.F1.Cocartesian.PullbackNativeLiftRestriction
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalDiagramOverIsomorphism
public import SerrePositivity.InfinityCategories.F1.Universe.OverIso
public import SerrePositivity.InfinityCategories.F1.Cocartesian.NativeHomPresentation

/-!
概要：元の任意の標準単体上の native Hom を、同じ分類先の区間 Hom と比較する。
方針：同じ底上の nerve 表示同型で、既存の有限セルの同じ局所比較を移す。
規約：元の標準単体と元の両端図式を保持する。
使われ方：境界の各面と各端点の実際の分類比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{u} C] {n : ℕ}
  (σ : (Δ[n] : SSet.{u}) ⟶ nerve C) (p q : CocartesianFibrationCategory (nerve C))
local notation "P" => cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => cocartesianStrictTransportCoherentDiagram q.val.hom

local instance (z : Over (nerve C)) : InnerFibration (pullback.fst z.hom q.val.hom) :=
  ⟨innerFibrations.pullback_fst z.hom q.val.hom (InnerFibration.mem (q := q.val.hom))⟩

local instance (z : Over (nerve C)) : KanComplex ((SSet.uliftFunctor.{u + 1, u}).obj
    ((cocartesianPullbackNativeCoreFunctor p.val.hom q.val.hom).obj (Opposite.op z))) :=
  inferInstanceAs (KanComplex ((SSet.uliftFunctor.{u + 1, u}).obj (quasicategoryCore
    (cocartesianRelativeFunctorSpace (pullback.fst z.hom p.val.hom)
      (pullback.fst z.hom q.val.hom)) : SSet.{u})))

/-- 同じ標準単体上の native Hom と、有限鎖表示の同じ Hom の同型。 -/
def cocartesianStandardSimplexSourceIso :
    (SSet.uliftFunctor.{u + 1, u}).obj
      ((cocartesianPullbackNativeCoreFunctor p.val.hom q.val.hom).obj (Opposite.op (Over.mk σ))) ≅
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (simplexNerveBaseFunctor σ))).obj p)
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (simplexNerveBaseFunctor σ))).obj q)) := by
  rw [cocartesianBaseChangeHom_nativePresentation (nerveMap (simplexNerveBaseFunctor σ)) p q]
  exact ((cocartesianPullbackNativeCoreFunctor p.val.hom q.val.hom) ⋙
    SSet.uliftFunctor.{u + 1, u}).mapIso (simplexNerveOverIso σ).symm.op

/-- 有限鎖上の分類先 Hom と、同じ標準単体上の分類先 Hom の同型。 -/
def cocartesianStandardSimplexTargetIso :
    intervalMappingSpace
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (simplexNerveBaseFunctor σ)) ≫ P))
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (simplexNerveBaseFunctor σ)) ≫ Q)) ≅
    intervalMappingSpace
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map σ ≫ P))
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map σ ≫ Q)) :=
  (intervalDiagramOverFunctor P Q).mapIso (uliftOverIso (simplexNerveOverIso σ)).op

/-- 同じ元の標準単体の native Hom から同じ分類先 Hom への実際の比較。 -/
def cocartesianStandardSimplexHomComparison :=
  (cocartesianStandardSimplexSourceIso σ p q).hom ≫
    cocartesianLocalHomComparison (simplexNerveBaseFunctor σ) p q ≫
      (cocartesianStandardSimplexTargetIso σ p q).hom

/-- Source の同型の順方向は、元の底上の逆同型による同じ直接制限。 -/
lemma cocartesianStandardSimplexSourceIso_hom :
    (cocartesianStandardSimplexSourceIso σ p q).hom =
      cocartesianPullbackNativeLiftPre p.val.hom q.val.hom (simplexNerveOverIso σ).inv := rfl

/-- Target の同型の順方向も、元の底上の同型による同じ直接制限。 -/
lemma cocartesianStandardSimplexTargetIso_hom :
    (cocartesianStandardSimplexTargetIso σ p q).hom =
      intervalDiagramOverPre P Q (uliftOverMorphism (simplexNerveOverIso σ).hom) := by
  change intervalDiagramOverPre P Q (uliftOverIso (simplexNerveOverIso σ)).hom = _
  rw [uliftOverIso_hom]

/-- 元の任意の標準単体上で、この同じ native 分類比較自身は同値。 -/
lemma cocartesianStandardSimplexHomComparison_isQCatEquivalence :
    IsQCatEquivalence (cocartesianStandardSimplexHomComparison σ p q) :=
  (qCatEquivalenceOfIso (cocartesianStandardSimplexSourceIso σ p q)).isQCatEquivalence.comp
    ((cocartesianLocalHomComparison_finite_isQCatEquivalence n (simplexNerveBaseFunctor σ) p q).comp
      (qCatEquivalenceOfIso (cocartesianStandardSimplexTargetIso σ p q)).isQCatEquivalence)

end SerrePositivity.InfinityCategories
