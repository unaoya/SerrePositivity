module

public import SerrePositivity.InfinityCategories.F2.Presentable.SmallContravariantHomContinuity
public import SerrePositivity.InfinityCategories.F2.Presentable.NativeSpaceUniverseReflection

/-!
概要：小さい反変 Hom 模型の連続性を無条件に回収する。
方針：指定宇宙変更による小さい錐の反映を利用する。
規約：元の Hom 模型と関手を保持し、充満忠実性を追加入力にしない。
使われ方：随伴関手定理の Hom 模型の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：元の反変 Hom の小さい模型は指定全極限を保つ。
方針：全表現可能前層の保存性を比較し、元の全錐へ反映する。
規約：存在する指定極限だけを扱い、極限の存在自体は仮定しない。
使われ方：反転余錐の保存性への接続。 -/
lemma smallContravariantHom_map_isLimit_native
    {C : SSet.{u + 1}} [Quasicategory C]
    (y : C _⦋0⦌)
    (H : C.op ⟶ SpaceInfinity.{u})
    (hH : FunctorIso (representablePresheafInfinity y)
      ((SSet.uliftFunctor.{u + 2, u + 1}).map H ≫ Compact.spaceUniverseDiagram))
    {K : SSet.{u}} {D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C.op}
    (c : JoinCone D) (hc : IsLimitCone c) :
    IsLimitCone (mapJoinCone H c) := by
  apply spaceUniverseDiagram_reflects_small_isLimit
  have h := representablePresheafInfinity_isLimit c hc y
  have h' : IsLimitCone (mapJoinCone
      ((SSet.uliftFunctor.{u + 2, u + 1}).map H ≫ Compact.spaceUniverseDiagram)
      (JoinCone.ulift.{u + 1, u + 2} c)) := h.of_functorIso
    (FunctorIso.precomp hH (JoinCone.ulift.{u + 1, u + 2} c).val)
  rw [mapJoinCone_universe_comp] at h'
  exact h'

/-- 概要：元の表現可能前層の小さい模型は連続。
方針：元の全余錐を反転し、指定全極限の保存を使う。
規約：元の小さい形状と全余錐を保持する。
使われ方：小さい反変 Hom へ表現可能性を適用するための保存性。 -/
lemma smallContravariantHom_sendsSmallColimitsToLimits_native
    {C : SSet.{u + 1}} [Quasicategory C]
    (y : C _⦋0⦌)
    (H : C.op ⟶ SpaceInfinity.{u})
    (hH : FunctorIso (representablePresheafInfinity y)
      ((SSet.uliftFunctor.{u + 2, u + 1}).map H ≫ Compact.spaceUniverseDiagram)) :
    SendsSmallColimitsToLimits H := by
  intro K D c hc
  exact smallContravariantHom_map_isLimit_native y H hH (K := K.op) (F1B.coconeReverseCone c)
    ((F1B.isColimitCone_iff_reverseCone c).mp hc)

/-- 概要：余極限保存関手との小さい反変 Hom 合成は連続。
方針：元の小さい Hom 模型の連続性を関手の反対に沿って制限する。
規約：元の関手 L を保持する。
使われ方：表現可能性から L の右随伴を構成する。 -/
lemma smallContravariantHomComposite_sendsSmallColimitsToLimits_native
    {C D : SSet.{u + 1}} [Quasicategory D]
    (L : C ⟶ D) (hL : PreservesSmallColimits L) (y : D _⦋0⦌)
    (H : D.op ⟶ SpaceInfinity.{u})
    (hH : FunctorIso (representablePresheafInfinity y)
      ((SSet.uliftFunctor.{u + 2, u + 1}).map H ≫ Compact.spaceUniverseDiagram)) :
    SendsSmallColimitsToLimits (SSet.opFunctor.map L ≫ H) :=
  (smallContravariantHom_sendsSmallColimitsToLimits_native y H hH).precomp_op L hL

end SerrePositivity.InfinityCategories.F2.Presentable
