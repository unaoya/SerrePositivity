module

public import SerrePositivity.InfinityCategories.F2.Presentable.SpaceUniverseLimits
public import SerrePositivity.InfinityCategories.F2.Compact.ConservativeLimitReflection
public import SerrePositivity.InfinityCategories.F2.Compact.UniverseConservativity
public import SerrePositivity.InfinityCategories.F1.Coherent.SpaceSmallLimits

/-!
概要：指定された空間の宇宙変更は小さい全図式の極限性を反映する。
方針：全切断による基準極限の保存と、元の辺の可逆性の反映を組み合わせる。
規約：元の指定錐を保持し、宇宙変更の充満忠実性を仮定しない。
使われ方：随伴関手定理の小さい Hom 模型の極限保存を回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：宇宙変更像が極限である元の小さい全錐は極限。
方針：同じ図式の全切断の錐と比較し、比較辺の可逆性を反映する。
規約：形状の quasicategory 性を追加しない。
使われ方：小さい空間値関手の全小極限保存の判定。 -/
lemma spaceUniverseDiagram_reflects_small_isLimit {I : SSet.{u}}
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ SpaceInfinity.{u}) (c : JoinCone D)
    (hc : IsLimitCone (mapJoinCone Compact.spaceUniverseDiagram (JoinCone.ulift c))) :
    IsLimitCone c := by
  let d := coherentDiagramSectionsCone D
  have hd : IsLimitCone d := coherentDiagramSectionsCone_isLimit D
  apply (isLimitCone_iff_ulift c).mpr
  exact Compact.isLimitCone_of_conservative_image Compact.spaceUniverseDiagram
    (fun e he ↦ Compact.spaceUniverseDiagram_reflects_invertibleEdge_native e he)
    (JoinCone.ulift d) (JoinCone.ulift c) ((isLimitCone_iff_ulift d).mp hd)
    (spaceUniverseDiagram_map_isLimit d hd) hc

end SerrePositivity.InfinityCategories.F2.Presentable
