module

public import SerrePositivity.InfinityCategories.F2.Compact.UniverseConservativity
public import SerrePositivity.InfinityCategories.F2.Compact.ConservativeColimitReflection
public import SerrePositivity.InfinityCategories.F2.Compact.UniverseColimits
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentTotalColimit

/-!
概要：指定された空間の宇宙変更は、元の小さい全図式の指定余錐の余極限性を反映する。
方針：同じ標準全空間余極限の保存と辺の可逆性の反映を用い、元の宇宙へ戻す。
規約：元の全図式と指定余錐そのものを保持する。
使われ方：Ind-S の小さい Hom 関手の κ-filtered 余極限保存の反映。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Compact
/-- 概要：元の小さい全図式の指定余錐の宇宙変更像が余極限なら、元の余錐も余極限。
方針：標準余極限との比較を保守性で反映する。
規約：同じ全余錐を保持。使われ方：P の小さい Hom の accessibility。 -/
lemma spaceUniverseDiagram_reflects_small_isColimit {I : SSet.{u}} [Quasicategory I]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ SpaceInfinity.{u}) (c : JoinCocone D)
    (hc : IsColimitCone (coconeUniverseImage c)) : IsColimitCone c := by
  let d := coherentDiagramTotalCocone D
  have hd : IsColimitCone d := coherentDiagramTotalCocone_isColimit D
  apply (isColimitCone_iff_ulift c).mpr
  apply isColimitCone_of_conservative_image spaceUniverseDiagram
    (fun e he ↦ spaceUniverseDiagram_reflects_invertibleEdge_native e he)
    (JoinCocone.ulift d) (JoinCocone.ulift c) ((isColimitCone_iff_ulift d).mp hd)
    (spaceUniverseDiagram_map_isColimit D d hd) hc
end SerrePositivity.InfinityCategories.F2.Compact
