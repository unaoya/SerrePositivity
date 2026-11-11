module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NativeFullRestriction
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.SphereClosureKernelMap

/-!
概要：実懸垂 data の resolved 関手間の全 Hom を、同じ実核の関手間へ送る。
方針：実証済みの安定核保存を使い、充満制限の全次数作用へ接続する。
規約：入力 A,B を動かす resolved 作用の存在はここでは仮定から導出しない。
使われ方：D-S の resolved 全 Hom 作用と D-4b の実核との接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory MonoidalCategory DifferentialGraded KST.SConstruction KST.NonConnective
variable (R : Type u) [CommRing R] (D E : Type (max (u + 1) v))
  [DGCategory R D] [DGCategory R E] [Small.{u} D] [Small.{u} E]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ) (J : DGKappaConeInput R E κ)

/-- 実 data の resolved 射を、実証済みの安定核保存とともに保持する。 -/
def dgKappaSuspensionKernelPreservingResolved (M : DGKappaSuspensionMapData R D E I J) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGFullPreservingFunctor R
      (DGCategoryCellResolution.Source R (DGKappaCone R D I))
      (DGCategoryCellResolution.Source R (DGKappaCone R E J))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureProperty R _
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureProperty R _
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGKappaCone R E J) (dgKappaConePerfectObjects R E J))) :=
  ⟨M.resolved, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaSuspensionMap_preservesKernel R D E I J M⟩

/-- 実 resolved 変換の任意複体パラメータを、同じ実核上で保持する。 -/
def dgKappaSuspensionKernelParameter
    (M N : DGKappaSuspensionMapData R D E I J) {K : Complex R}
    (τ : DGFunctorParamTrans R _ _ K M.resolved N.resolved) :
    DGFunctorParamTrans R _ _ K
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaSuspensionKernelFunctor R D E I J M)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaSuspensionKernelFunctor R D E I J N) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgFullRestrictionParameter R _ _ _ _
    (dgKappaSuspensionKernelPreservingResolved R D E I J M)
    (dgKappaSuspensionKernelPreservingResolved R D E I J N) τ

/-- 全次数の核変換成分は元の resolved 変換の同じ実対象での成分そのもの。 -/
lemma dgKappaSuspensionKernelParameter_app
    (M N : DGKappaSuspensionMapData R D E I J) {K : Complex R}
    (τ : DGFunctorParamTrans R _ _ K M.resolved N.resolved)
    (x : dgKappaResolvedKernelKInput R D I) :
    (dgKappaSuspensionKernelParameter R D E I J M N τ).app x = τ.app x.val := rfl

/-- 実 resolved 関手間の Hom end から、同じ核関手間の Hom end への鎖写像。 -/
def dgKappaSuspensionKernelHom (M N : DGKappaSuspensionMapData R D E I J) :
    dgFunctorHom R _ _ M.resolved N.resolved ⟶
      dgFunctorHom R _ _ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaSuspensionKernelFunctor R D E I J M)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaSuspensionKernelFunctor R D E I J N) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgFullRestrictionHom R _ _ _ _
    (dgKappaSuspensionKernelPreservingResolved R D E I J M)
    (dgKappaSuspensionKernelPreservingResolved R D E I J N)

@[reassoc (attr := simp)]
lemma dgKappaSuspensionKernelHom_π (M N : DGKappaSuspensionMapData R D E I J)
    (x : dgKappaResolvedKernelKInput R D I) :
    dgKappaSuspensionKernelHom R D E I J M N ≫ dgFunctorHomπ R _ _ _ _ x =
      dgFunctorHomπ R _ _ M.resolved N.resolved x.val :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgFullRestrictionHom_π R _ _ _ _ _ _ x

/-- 全 Hom の単位元も同じ実核上で厳密に保存する。 -/
lemma dgKappaSuspensionKernelHom_identity (M : DGKappaSuspensionMapData R D E I J) :
    dgFunctorIdentity R _ _ M.resolved ≫ dgKappaSuspensionKernelHom R D E I J M M =
      dgFunctorIdentity R _ _ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaSuspensionKernelFunctor R D E I J M) := by
  apply dgFunctorHom_ext
  intro x
  rw [Category.assoc, dgKappaSuspensionKernelHom_π, dgFunctorIdentity_π,
    dgFunctorIdentity_π]
  rfl

set_option maxHeartbeats 800000 in
-- 具体的 cell 分解と核の Hom end の型照合に既定の heartbeat 上限以上を要する。
/-- 全 Hom end の縦合成を、同じ tensor パラメータのまま厳密に保存する。 -/
lemma dgKappaSuspensionKernelHom_composition
    (M N P : DGKappaSuspensionMapData R D E I J) :
    dgFunctorComposition R
        (DGCategoryCellResolution.Source R (DGKappaCone R D I))
        (DGCategoryCellResolution.Source R (DGKappaCone R E J))
        M.resolved N.resolved P.resolved ≫
        dgKappaSuspensionKernelHom R D E I J M P =
      (dgKappaSuspensionKernelHom R D E I J M N ⊗ₘ
        dgKappaSuspensionKernelHom R D E I J N P) ≫
        dgFunctorComposition R (dgKappaResolvedKernelKInput R D I)
          (dgKappaResolvedKernelKInput R E J)
          (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaSuspensionKernelFunctor R D E I J M)
          (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaSuspensionKernelFunctor R D E I J N)
          (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaSuspensionKernelFunctor R D E I J P) := by
  apply dgFunctorHom_ext
  intro x
  simp only [Category.assoc, dgKappaSuspensionKernelHom_π, dgFunctorComposition_π,
    tensorHom_comp_tensorHom_assoc]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
