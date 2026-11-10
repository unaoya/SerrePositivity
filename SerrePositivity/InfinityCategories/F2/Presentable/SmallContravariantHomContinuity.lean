module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessibleSmallContravariantHom
public import SerrePositivity.InfinityCategories.F2.Presentable.NativeUniverseReflection

/-!
概要：小さい反変 Hom 模型が小余極限を小極限へ送ることを宇宙変更の反映から回収する。
方針：元の全表現可能前層の極限保存を指定自然同型で移し、同じ全錐へ反映する。
規約：指定宇宙変更の充満忠実性を明示し、その存在はここでは主張しない。
使われ方：余極限保存関手の Hom 合成に表現可能性を適用する。
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
lemma smallContravariantHom_map_isLimit
    {C : SSet.{u + 1}} [Quasicategory C]
    (hU : IsFullyFaithful Compact.spaceUniverseDiagram.{u}) (y : C _⦋0⦌)
    (H : C.op ⟶ SpaceInfinity.{u})
    (hH : FunctorIso (representablePresheafInfinity y)
      ((SSet.uliftFunctor.{u + 2, u + 1}).map H ≫ Compact.spaceUniverseDiagram))
    {K : SSet.{u + 1}} {D : K ⟶ C.op} (c : JoinCone D) (hc : IsLimitCone c) :
    IsLimitCone (mapJoinCone H c) := by
  apply (isLimitCone_iff_ulift.{u + 1, u + 2} (mapJoinCone H c)).mpr
  apply isLimitCone_of_fullyFaithful_image Compact.spaceUniverseDiagram hU
  have h := representablePresheafInfinity_isLimit c hc y
  have h' : IsLimitCone (mapJoinCone
      ((SSet.uliftFunctor.{u + 2, u + 1}).map H ≫ Compact.spaceUniverseDiagram)
      (JoinCone.ulift.{u + 1, u + 2} c)) := h.of_functorIso
    (FunctorIso.precomp hH (JoinCone.ulift.{u + 1, u + 2} c).val)
  rw [mapJoinCone_universe_comp] at h'
  exact h'

/-- 概要：元の表現可能前層の小さい模型は反映界面の下で連続。
方針：元の全余錐を反転し、指定全極限の保存を使う。
規約：元の小さい形状と全余錐を保持する。
使われ方：小さい反変 Hom へ表現可能性を適用するための保存性。 -/
lemma smallContravariantHom_sendsSmallColimitsToLimits
    {C : SSet.{u + 1}} [Quasicategory C]
    (hU : IsFullyFaithful Compact.spaceUniverseDiagram.{u}) (y : C _⦋0⦌)
    (H : C.op ⟶ SpaceInfinity.{u})
    (hH : FunctorIso (representablePresheafInfinity y)
      ((SSet.uliftFunctor.{u + 2, u + 1}).map H ≫ Compact.spaceUniverseDiagram)) :
    SendsSmallColimitsToLimits H := by
  intro K D c hc
  exact smallContravariantHom_map_isLimit hU y H hH (F1B.coconeReverseCone c)
    ((F1B.isColimitCone_iff_reverseCone c).mp hc)

/-- 概要：余極限保存関手との小さい反変 Hom 合成は反映界面の下で連続。
方針：元の小さい Hom 模型の連続性を関手の反対に沿って制限する。
規約：元の関手 L を保持する。
使われ方：表現可能性から L の右随伴を構成する。 -/
lemma smallContravariantHomComposite_sendsSmallColimitsToLimits
    {C D : SSet.{u + 1}} [Quasicategory D]
    (hU : IsFullyFaithful Compact.spaceUniverseDiagram.{u})
    (L : C ⟶ D) (hL : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits L) (y : D _⦋0⦌)
    (H : D.op ⟶ SpaceInfinity.{u})
    (hH : FunctorIso (representablePresheafInfinity y)
      ((SSet.uliftFunctor.{u + 2, u + 1}).map H ≫ Compact.spaceUniverseDiagram)) :
    SendsSmallColimitsToLimits (SSet.opFunctor.map L ≫ H) :=
  (smallContravariantHom_sendsSmallColimitsToLimits hU y H hH).precomp_op L hL

end SerrePositivity.InfinityCategories.F2.Presentable
