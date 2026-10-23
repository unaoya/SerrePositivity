module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.OneBoundaryProduct
public import SerrePositivity.InfinityCategories.F1.Cocartesian.OneHornOriginal
public import SerrePositivity.InfinityCategories.HomotopyLimits.TensorHomotopyEquivalence

/-!
概要：一次元標準境界の元の native Hom から、同じ分類先の区間 Hom への実際の比較同値。
方針：両端の同じ零次元比較を直積にし、両側の実際の境界 Hom の積分解で戻す。
規約：元の両端への制限を保持する。
使われ方：境界全体の比較の帰納の一次元の初期値。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
attribute [local instance] HomotopyLimits.kanTensor_isKan
variable {C : Type u} [Category.{u} C] (i : Fin 2) (σ : (Δ[1] : SSet.{u}) ⟶ nerve C)
  (p q : CocartesianFibrationCategory (nerve C))
local notation "P" => cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => cocartesianStrictTransportCoherentDiagram q.val.hom

local instance {D : SSet.{u}} (a : D ⟶ nerve C) : InnerFibration (pullback.fst a q.val.hom) :=
  ⟨innerFibrations.pullback_fst a q.val.hom (InnerFibration.mem (q := q.val.hom))⟩

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

/-- 元の両端の同じ比較を貼って作る、一次元標準境界全体の実際の比較。 -/
def cocartesianOneBoundaryHomComparison :=
  (cocartesianOneBoundaryNativeProductIso i σ p.val.hom q.val.hom).hom ≫
    (cocartesianStandardSimplexHomComparison (stdSimplex.δ i ≫ σ) p q ⊗ₘ
      cocartesianOneHornHomComparison i σ p q) ≫
    (cocartesianOneBoundaryIntervalProductIso i σ P Q).inv

/-- 元の一次元標準境界全体で、この同じ比較自身が同値。 -/
lemma cocartesianOneBoundaryHomComparison_isQCatEquivalence :
    IsQCatEquivalence (cocartesianOneBoundaryHomComparison i σ p q) :=
  (qCatEquivalenceOfIso
    (cocartesianOneBoundaryNativeProductIso i σ p.val.hom q.val.hom)).isQCatEquivalence.comp
      ((HomotopyLimits.tensor_isQCatEquivalence
        (cocartesianStandardSimplexHomComparison_isQCatEquivalence (stdSimplex.δ i ≫ σ) p q)
        (cocartesianOneHornHomComparison_isQCatEquivalence i σ p q)).comp
        (qCatEquivalenceOfIso (cocartesianOneBoundaryIntervalProductIso i σ P Q).symm).isQCatEquivalence)

end SerrePositivity.InfinityCategories
