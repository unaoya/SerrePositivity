module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaUniverseYoneda
public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafUniverseColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaKanCoconeComparison

/-!
概要：指定された大きい前層値関手は、元の各 P_Σ 頂点の全密度余錐を余極限へ送る。
方針：元の包含像を元の前層密度余錐へ厳密に照合し、宇宙変更の小余極限保存を使う。
規約：元の指定頂点・密度図式・全余錐を保持。有限余積の存在を要求しない。
使われ方：大きい係数前層への全自然変換空間の局所右 Kan 条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の包含は、同じ指定頂点の全密度余錐を同じ前層圏の余極限へ送る。 -/
lemma sigmaVertexDensity_inclusion_isColimit {C : SSet.{u}} [Quasicategory C]
    (v : (SigmaPresheafInfinity C) _⦋0⦌) :
    IsColimitCone (mapJoinCocone (sigmaPresheafInfinityInclusion C)
      (sigmaVertexDensityCocone v)) :=
  (F2.isColimitCone_iff_of_cocone_val_eq _ _
    (sigmaVertexDensityCocone_val_inclusion v)).mpr
    (F2.Ind.presheafDensityCocone_isColimit (sigmaPresheafVertexFunctor v))

/-- 同じ大きい前層値関手は、元の指定全密度余錐の持ち上げを余極限へ送る。 -/
lemma sigmaUniverseInclusion_density_isColimit {C : SSet.{u}} [Quasicategory C]
    (v : (SigmaPresheafInfinity C) _⦋0⦌) :
    IsColimitCone (mapJoinCocone (sigmaUniverseInclusion C)
      (JoinCocone.ulift.{u + 1, u + 2} (sigmaVertexDensityCocone v))) := by
  rw [sigmaUniverseInclusion, F2.Compact.mapJoinCocone_universe_comp]
  exact presheafUniverseDiagram_map_isColimit _ _ (sigmaVertexDensity_inclusion_isColimit v)

end SerrePositivity.InfinityCategories.HomotopyLimits
