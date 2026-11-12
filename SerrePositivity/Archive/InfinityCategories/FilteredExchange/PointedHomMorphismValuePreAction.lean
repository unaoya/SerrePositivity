module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoCurryComponentPreAction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedHomMorphismPrismComponent
/-!
概要：元の固定射の値比較の前作用を、元の同じ実 prism の指定対角値へ戻す。
方針：構成時の表示変更を保持して curry の指定成分と同じ係数制限を合成する。
規約：元の VertexIso・固定射・全係数を保持する。
使われ方：Ncomp の最大化側の値と元の最後射の値比較の接続。
-/

@[expose] public section
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial

noncomputable section
namespace SerrePositivity.InfinityCategories.F2
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K L : KanObject.{u}} (f : K ⟶ L)
local notation "A" => CategoryTheory.Functor.obj SSet.uliftFunctor
  (CategoryTheory.Functor.obj SSet.opFunctor (SimplicialCategory.sHom pointKanObject K))
local notation "H" => CategoryTheory.Functor.obj SSet.uliftFunctor
  (CategoryTheory.Functor.obj SSet.opFunctor (SimplicialCategory.sHom K L))
local notation "r" => lift (𝟙 A) (SSet.const (ULift.up (SSet.opObjEquiv.symm (functorVertex f))))
local notation "x" => fst A H ≫ Iso.hom
  (uliftOppositeIso (SimplicialCategory.sHom pointKanObject K))
local notation "y" => snd A H ≫ Iso.hom (uliftOppositeIso (SimplicialCategory.sHom K L))
local notation "p" => pointedSpaceProjection
local notation "c" => pointedReverseKanFiberComparison K
local notation "γ" => pointedReverseKanHomInterval K L
local notation "h₀" => pointedReverseKanHomInterval_zero K L
local notation "h₁" => pointedReverseKanHomInterval_one K L
local notation "T" => pointedReverseKanCompositionTransportFamily K L
local notation "v" => y ≫ intervalMappingCurryOfEndpoints γ h₀ h₁
local notation "V" => QCatEquivalence.hom
  (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L))


local notation "Y" => CategoryTheory.Functor.obj SSet.uliftFunctor (KanObject.obj L)
/-- 概要：元の値比較の前作用は同じ左全対角の係数制限。
方針：構成時の表示変更を除き、同じ curry 成分の前作用を計算する。
規約：元の指定成分を保持。使われ方：実 prism 表示への帰還。 -/
lemma pointedHomMorphismValueComparison_map_pre_heq_left_diagonal
    {D : SSet.{u + 1}} (q : D ⟶ A) :
    HEq (VertexIso.map (pointedHomMorphismValueComparison f) ((pre q).app Y))
      ((pointedLeftHomDiagonalValueIso K L (fst A H) (snd A H)).precomp (q ≫ r)) := by
  rw [pointedHomMorphismValueComparison_eq_left f]
  unfold pointedHomMorphismLeftValueComparison
  refine (vertexIsoOfEq_map_heq _ _ _ _).trans ?_
  unfold pointedLeftHomValueActionIso
  exact functorIsoOfEq_curry_app_map_pre_heq _ _ _ _ q
/-- 概要：元の値比較の前作用は同じ実 prism の指定対角値の係数制限。
方針：同じ全比較の表示変更と実 prism 表示を合成する。
規約：元の全係数を保持。使われ方：Ncomp の値比較。 -/
lemma pointedHomMorphismValueComparison_map_pre_heq_prism
    {D : SSet.{u + 1}} (q : D ⟶ A) :
    HEq (VertexIso.map (pointedHomMorphismValueComparison f) ((pre q).app Y))
      (((leftFibrationPrism_diagonalTransportIso p (x ≫ c)
        (lift x y ≫ FiberTransportFamily.endpoint T)
        (intervalMappingUncurry v) (intervalMappingUncurry_zero v) (intervalMappingUncurry_one v)
        ((Δ[1] ◁ lift x y) ≫ FiberTransportFamily.prism T)
        (fiberTransportDiagonalPrism_start p c γ T x y)
        (fiberTransportDiagonalPrism_finish p c γ T x y)
        (fiberTransportDiagonalPrism_projection p c γ h₀ h₁ T x y)).postcomp V).precomp (q ≫ r)) := by
  refine (pointedHomMorphismValueComparison_map_pre_heq_left_diagonal f q).trans ?_
  refine (pointedLeftHomDiagonalValueIso_precomp_heq_reverse K L (fst A H) (snd A H)
    (q ≫ r)).trans ?_
  refine (pointedReverseKanDiagonalValueIso_precomp_heq_diagonal K L (fst A H) (snd A H)
    (q ≫ r)).trans ?_
  exact fiberTransportDiagonalIso_postcomp_precomp_heq_prism p c γ h₀ h₁ T x y V (q ≫ r)
end SerrePositivity.InfinityCategories.F2
