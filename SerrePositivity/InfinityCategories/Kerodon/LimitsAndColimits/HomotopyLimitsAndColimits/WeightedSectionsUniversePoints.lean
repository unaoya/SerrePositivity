module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedSectionsUniverseIso

/-!
概要：元の指定重み付き錐の零単体を、同じ切断空間の宇宙比較射で追跡する。
方針：標準零単体のYoneda写像を宇宙変更し、同じ普遍評価の転置を照合する。
規約：IS-W2 R02〜R03の係数移送の点での法則。π₀への弱化なし。
使われ方：同じ普遍BK点をHom∞比較の宇宙へ運ぶ。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open CategoryTheory Limits SSet MonoidalCategory CartesianMonoidalCategory
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

/-- 元の零単体パラメーターの同じ宇宙変更は、第一射影を厳密に保つ。 -/
@[reassoc] theorem weightedDiagramUniverseTensorIso_zero_fst (W : I ⥤ SSet.{u}) :
    ((weightedDiagramUniverse.{u,v} I).obj W ◁ (Functor.const (AsSmall.{v} I)).map
      (uliftStdSimplexIso.{u,max u v} 0).inv) ≫
        (weightedDiagramUniverseTensorIso I W (Δ[0] : SSet.{u})).inv ≫
          (weightedDiagramUniverse I).map (fst W ((Functor.const I).obj (Δ[0] : SSet.{u}))) =
      fst ((weightedDiagramUniverse.{u,v} I).obj W)
        ((Functor.const (AsSmall.{v} I)).obj (Δ[0] : SSet.{max u v})) := by
  apply NatTrans.ext
  funext i
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨w, t⟩
  rfl

/-- 同じ指定宇宙比較は、元の錐の零単体を同じ宇宙変更した錐の零単体へ送る。 -/
theorem weightedSectionsUniverseComparison_point {W H : I ⥤ SSet.{u}} (s : W ⟶ H) :
    ((weightedSectionsUniverseComparison.{u,v} I W H).app (Opposite.op ⦋0⦌))
      (ULift.up (SSet.yonedaEquiv (weightedSectionsLift
        (fst W ((Functor.const I).obj (Δ[0] : SSet.{u})) ≫ s)))) =
        SSet.yonedaEquiv (weightedSectionsLift
          (fst ((weightedDiagramUniverse.{u,v} I).obj W)
            ((Functor.const (AsSmall.{v} I)).obj (Δ[0] : SSet.{max u v})) ≫
              (weightedDiagramUniverse.{u,v} I).map s)) := by
  let q := weightedSectionsLift (fst W ((Functor.const I).obj (Δ[0] : SSet.{u})) ≫ s)
  let r := (uliftStdSimplexIso.{u,max u v} 0).inv ≫
    ((SSet.uliftFunctor.{max u v,u}).map q ≫ weightedSectionsUniverseComparison I W H)
  have hr : r = weightedSectionsLift
      (fst ((weightedDiagramUniverse.{u,v} I).obj W)
        ((Functor.const (AsSmall.{v} I)).obj (Δ[0] : SSet.{max u v})) ≫
          (weightedDiagramUniverse.{u,v} I).map s) := by
    apply (weightedSectionsHomEquiv ((weightedDiagramUniverse.{u,v} I).obj W)
      ((weightedDiagramUniverse.{u,v} I).obj H) (Δ[0] : SSet.{max u v})).injective
    change weightedSectionsUncurry r = weightedSectionsUncurry (weightedSectionsLift _)
    dsimp only [r, q]
    rw [weightedSectionsUncurry_precomp, weightedSectionsUniverseComparison_map_uncurry,
      weightedSectionsUncurry_lift, weightedSectionsUncurry_lift,
      CategoryTheory.Functor.map_comp, weightedDiagramUniverseTensorIso_zero_fst_assoc]
  have hu := uliftYonedaMap.{u,max u v} (SSet.yonedaEquiv q)
  rw [Equiv.symm_apply_apply] at hu
  have hp : SSet.yonedaEquiv r =
      ((weightedSectionsUniverseComparison.{u,v} I W H).app (Opposite.op ⦋0⦌))
        (ULift.up (SSet.yonedaEquiv q)) := by
    dsimp only [r]
    rw [← Category.assoc, hu, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  exact hp.symm.trans (congrArg SSet.yonedaEquiv hr)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
