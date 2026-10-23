module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedRightFamilyCounitSquare
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedValueFamilyCounitNaturality

/-!
概要：元の全値比較に右 Hom の元の逆射を入力し、同じ余単位と全右 Hom 比較へ整理する。
方針：元の三因子を保持し、同じ余単位正方形と終点余単位の自然性を合成する。
規約：元の値比較を置き換えない。使われ方：元の長辺比較と全右 Hom 成分との照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {K L : KanObject.{u}} {P : SSet.{u + 1}}
  (x : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj K.obj)
  (y : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L))
local notation "V₀" => QCatEquivalence.hom
  (pointedSpaceFiberValueEquivalence (spaceInfinityVertex K))
local notation "V₁" => QCatEquivalence.hom
  (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L))
local notation "q" => x ≫ pointedRightFiberComparison K
local notation "a" => pointedValueFamilyTargetCounitIso K x
local notation "b" => pointedRightFamilyEvaluationValueIso (K := K) (L := L) a y
local notation "v₀" => pointedRightFamilyEvaluation (K := K) (L := L) (q ≫ V₀) y
local notation "v₁" => pointedRightFamilyEvaluation (K := K) (L := L) x y
local notation "E" => FiberTransportFamily.endpoint (parametrizedFiberTransportFamily
  pointedSpaceProjection (spaceInfinityVertex K) (spaceInfinityVertex L))
local notation "S" => FunctorIso.postcomp (functorIsoLiftRight
  (pointedValueFamilySourceUnitIso K q) (y ≫ coherentKanRightHomInterval K L)) E
local notation "B" => FunctorIso.postcomp
  (pointedRightFamilyTransportIso (K := K) (L := L) (q ≫ V₀) y) V₁
local notation "C" => FunctorIso.postcomp
  (pointedRightFamilyTransportIso (K := K) (L := L) x y) V₁

/-- 元の右 Hom で戻した全点の値比較は、同じ評価余単位・終点余単位・全比較の三因子。 -/
lemma pointedValueFamilyTransportIso_at_right :
    pointedValueFamilyTransportIso (K := K) (L := L) q y =
      b ≪≫ (pointedValueFamilyTargetCounitIso L v₁).symm ≪≫ C := by
  rw [pointedValueFamilyTransportIso_factorization]
  have h := congrArg (fun e => FunctorIso.postcomp e V₁)
    (pointedRightFamilyTransportIso_counit_square x y)
  simp only [functorIso_postcomp_trans] at h
  calc
    _ = (pointedValueFamilyTargetCounitIso L v₀).symm ≪≫
        (B ≪≫ FunctorIso.postcomp S V₁) := by simp only [Iso.trans_assoc]
    _ = (pointedValueFamilyTargetCounitIso L v₀).symm ≪≫
        (FunctorIso.postcomp (FunctorIso.postcomp b (pointedRightFiberComparison L)) V₁ ≪≫ C) := by
      rw [← h]
    _ = ((pointedValueFamilyTargetCounitIso L v₀).symm ≪≫
        FunctorIso.postcomp (FunctorIso.postcomp b (pointedRightFiberComparison L)) V₁) ≪≫ C :=
      (Iso.trans_assoc _ _ _).symm
    _ = (b ≪≫ (pointedValueFamilyTargetCounitIso L v₁).symm) ≪≫ C := by
      rw [pointedValueFamilyTargetCounitIso_conjugation]
    _ = _ := Iso.trans_assoc _ _ _

end SerrePositivity.InfinityCategories.F2
