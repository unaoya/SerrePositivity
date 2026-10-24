module

public import SerrePositivity.InfinityCategories.F2.Presentable.SiftedSimplexCategory
public import SerrePositivity.InfinityCategories.F2.Presentable.CoproductRealizationConditions
public import SerrePositivity.InfinityCategories.F2.Presentable.SiftedColimitPreservation

/-!
概要：P_Σ の幾何学的実現の存在と元の包含による保存。
方針：反対単体圏の sifted 性を既存の全 sifted 余極限へ適用する。
規約：元の全単体的図式と指定全余錐を保持する。
使われ方：P_Σ 専用反映と simplicial Ind 表示。
-/

@[expose] public section
universe u
open CategoryTheory SSet
attribute [local instance] CategoryTheory.uliftCategory
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：P_Σ は小さい幾何学的実現を持つ。
方針：反対単体圏の元の sifted 性から既存の存在定理を使う。
規約：全小余極限の存在を入力にしない。
使われ方：専用反映の小余極限の構成。 -/
lemma sigma_hasSmallGeometricRealizations (C : SSet.{u}) :
    HasSmallGeometricRealizations (HomotopyLimits.SigmaPresheafInfinity C) :=
  HomotopyLimits.sigma_hasSmallSiftedColimits C _

/-- 概要：P_Σ の元の包含は同じ指定幾何学的実現を保存する。
方針：元の反対単体添字の sifted 性を保存定理へ渡す。
規約：元の全余錐を別の模型へ取り替えない。
使われ方：反映した bar 表示の全前層圏内の実現。 -/
lemma sigmaInclusion_geometricRealization_isColimit {C : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve SmallSimplexOpposite.{u}) ⟶
      HomotopyLimits.SigmaPresheafInfinity C)
    (c : JoinCocone F) (hc : IsColimitCone c) :
    IsColimitCone (mapJoinCocone (HomotopyLimits.sigmaPresheafInfinityInclusion C) c) :=
  HomotopyLimits.sigmaInclusion_map_isColimit F c hc

end SerrePositivity.InfinityCategories.F2.Presentable
