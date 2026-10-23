module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitApexLongRawValueRatio
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitApexPointedLongNativeComposition
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorIsoPrePostSourceDisplay
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorIsoDownHorizontal

/-!
概要：元の実長辺比較と raw 長辺値比較の合成を、同じ普遍直接比較へ接続する。
方針：実結合表示を固定し、同じ raw 二因子の比を合成して第一因子を消去する。
規約：元の指定値・全係数を保持。使われ方：元の長辺評価比較との同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "q" => coherentColimitApexCoefficientMap B T
local notation "g" => coherentColimitApexTargetCoefficientMap B T
local notation "D" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B d)
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "V₀" => pointedFiberValueTo (coherentColimitApex_raw_zero_vertex B T)
local notation "V₂" => pointedFiberValueTo (coherentColimitApex_raw_two_vertex B T)
local notation "f" => coherentEdgeHom (SpaceInfinity.δ 1 (coherentColimitApexTriangle B T))
local notation "E" => Equiv.symm (functorVertexEquiv _ _)
  (NatTrans.app (parametrizedFiberTransport pointedSpaceProjection
    (JoinCocone.vertex (coherentDiagramTotalCocone F))
    (JoinCocone.vertex (coherentDiagramTotalCocone J))) (Opposite.op ⦋0⦌)
      (NatTrans.app D (Opposite.op ⦋0⦌) l))
local notation "R" => coherentColimitApexLongRawValueRatio B T

/-- 元の全実長辺比較と同じ raw 長辺値比較の、始点表示を保つ元の指定合成。 -/
def coherentColimitApexLongValueComposite :
    FunctorIso (g ≫ V₂) (q ≫ (V₀ ≫ (SSet.uliftFunctor.{u + 1, u}).map f)) :=
  (coherentColimitApexPointedLongComparison B T).postcomp V₂ ≪≫
    functorIsoOfEq ((coherentColimitApexRawLongValueIso B T).precomp q)
      (Category.assoc q (coherentColimitRawFiberTransport B d) V₂).symm rfl

/-- 同じ raw 二因子の比を続けると、元の指定直接比較の値へ厳密に戻る。 -/
lemma coherentColimitApexLongValueComposite_trans_ratio :
    coherentColimitApexLongValueComposite B T ≪≫ R =
      functorIsoOfEq ((coherentColimitApexPointedLongNativeComparison B T).postcomp V₂)
        rfl (Category.assoc q E V₂) := by
  let L := (coherentColimitApexPointedLongComparison B T).postcomp V₂
  let V := (coherentColimitApexRawLongValueIso B T).precomp q
  let U := pointedIntervalTransportAt_universalIso D l
  have hb := (Category.assoc q (coherentColimitRawFiberTransport B d) V₂).symm
  have hn := congrArg (fun e => FunctorIso.postcomp e V₂)
    (coherentColimitApexPointedLongComparison_trans_universal B T)
  rw [functorIso_postcomp_trans] at hn
  change (L ≪≫ functorIsoOfEq V hb rfl) ≪≫ R = _
  calc
    _ = L ≪≫ (functorIsoOfEq V hb rfl ≪≫ R) := Iso.trans_assoc _ _ _
    _ = L ≪≫ functorIsoOfEq (V ≪≫ R) hb rfl :=
      congrArg (fun e => L ≪≫ e) (functorIsoOfEq_trans V R hb rfl rfl).symm
    _ = L ≪≫ functorIsoOfEq ((U.postcomp V₂).precomp q) hb rfl :=
      congrArg (fun e => L ≪≫ functorIsoOfEq e hb rfl)
        (coherentColimitApexLongRawValueRatio_cancel B T)
    _ = L ≪≫ functorIsoOfEq ((U.precomp q).postcomp V₂) rfl
        (Category.assoc q E V₂) :=
      congrArg (fun e => L ≪≫ e)
        (functorIso_post_pre_source_eq_pre_post_target U q V₂)
    _ = functorIsoOfEq (L ≪≫ (U.precomp q).postcomp V₂) rfl
        (Category.assoc q E V₂) :=
      (functorIsoOfEq_trans L ((U.precomp q).postcomp V₂) rfl rfl
        (Category.assoc q E V₂)).symm
    _ = _ := congrArg (fun e => functorIsoOfEq e rfl (Category.assoc q E V₂)) hn

end SerrePositivity.InfinityCategories.F2
