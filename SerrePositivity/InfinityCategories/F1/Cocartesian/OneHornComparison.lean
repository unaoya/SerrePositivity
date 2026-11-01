module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.StandardSimplexOriginal
public import SerrePositivity.InfinityCategories.Simplicial.HornOnePointIso

/-!
概要：一次元境界のホーン側の元の native Hom を、同じ分類先 Hom と比較する。
方針：同じ標準点の表示同型で、元の零次元セルの比較を移す。
規約：元のホーン・元の全 Hom・同じ底上の制限を保持する。
使われ方：一次元境界の両端の同値の貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{u} C] (i : Fin 2) (σ : (Δ[1] : SSet.{u}) ⟶ nerve C)
  (p q : CocartesianFibrationCategory (nerve C))
local notation "P" => cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => cocartesianStrictTransportCoherentDiagram q.val.hom

local instance (z : Over (nerve C)) : InnerFibration (pullback.fst z.hom q.val.hom) :=
  ⟨innerFibrations.pullback_fst z.hom q.val.hom (InnerFibration.mem (q := q.val.hom))⟩

local instance (z : Over (nerve C)) : KanComplex ((SSet.uliftFunctor.{u + 1, u}).obj
    ((cocartesianPullbackNativeCoreFunctor p.val.hom q.val.hom).obj (Opposite.op z))) :=
  inferInstanceAs (KanComplex ((SSet.uliftFunctor.{u + 1, u}).obj (quasicategoryCore
    (cocartesianRelativeFunctorSpace (pullback.fst z.hom p.val.hom)
      (pullback.fst z.hom q.val.hom)) : SSet.{u})))

local instance (z : Over (nerve C)) : KanComplex
    (((cocartesianPullbackNativeCoreFunctor p.val.hom q.val.hom) ⋙
      SSet.uliftFunctor.{u + 1, u}).obj (Opposite.op z)) :=
  inferInstanceAs (KanComplex ((SSet.uliftFunctor.{u + 1, u}).obj
    ((cocartesianPullbackNativeCoreFunctor p.val.hom q.val.hom).obj (Opposite.op z))))

local instance (z : Over ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C))) :
    KanComplex ((intervalDiagramOverFunctor P Q).obj (Opposite.op z)) :=
  inferInstanceAs (KanComplex (intervalMappingSpace
    (functorVertex (z.hom ≫ P)) (functorVertex (z.hom ≫ Q))))

/-- 元のホーンの native core を同じ標準点上の native core へ移す同型。 -/
def cocartesianOneHornSourceIso :=
  ((cocartesianPullbackNativeCoreFunctor p.val.hom q.val.hom) ⋙
    SSet.uliftFunctor.{u + 1, u}).mapIso (hornOnePointOverIso i σ).op

/-- 同じ標準点上の分類先 Hom を元のホーン上の分類先 Hom へ戻す同型。 -/
def cocartesianOneHornTargetIso :=
  (intervalDiagramOverFunctor P Q).mapIso (uliftOverIso (hornOnePointOverIso i σ)).symm.op

/-- 元のホーンの native Hom から、同じ分類先 Hom への実際の比較。 -/
def cocartesianOneHornHomComparison :=
  (cocartesianOneHornSourceIso i σ p q).hom ≫
    cocartesianStandardSimplexHomComparison (hornOnePointMap i σ) p q ≫
      (cocartesianOneHornTargetIso i σ p q).hom

/-- 元のホーン側の同じ実際の比較自身は同値。 -/
lemma cocartesianOneHornHomComparison_isQCatEquivalence :
    IsQCatEquivalence (cocartesianOneHornHomComparison i σ p q) :=
  (qCatEquivalenceOfIso (cocartesianOneHornSourceIso i σ p q)).isQCatEquivalence.comp
    ((cocartesianStandardSimplexHomComparison_isQCatEquivalence (hornOnePointMap i σ) p q).comp
      (qCatEquivalenceOfIso (cocartesianOneHornTargetIso i σ p q)).isQCatEquivalence)

/-- 同じ source 表示同型の射は、元の底上の同型による同じ直接制限。 -/
lemma cocartesianOneHornSourceIso_hom :
    (cocartesianOneHornSourceIso i σ p q).hom =
      cocartesianPullbackNativeLiftPre p.val.hom q.val.hom (hornOnePointOverIso i σ).hom := rfl

/-- 同じ target 表示同型の射も、元の底上の逆同型による同じ直接制限。 -/
lemma cocartesianOneHornTargetIso_hom :
    (cocartesianOneHornTargetIso i σ p q).hom =
      intervalDiagramOverPre P Q (uliftOverMorphism (hornOnePointOverIso i σ).inv) := by
  change intervalDiagramOverPre P Q (uliftOverIso (hornOnePointOverIso i σ)).inv = _
  rw [uliftOverIso_inv]

end SerrePositivity.InfinityCategories
