module
public import SerrePositivity.EInfinity.HomotopyWeight.NativeWeightedPointRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SectionFiberEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanSectionsIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedSectionParameter
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveFiber

/-!
概要：元の指定BK点をweighted nerveの同じfiberで評価すると、恒等射での元の係数を回収する。
方針：元の切断の普遍評価とパラメーター自然性を用い、同じ零単体の初区間を計算する。
規約：IS-W2 R02〜R03の既存構成の評価・単位則。Kan性の追加なし。
使われ方：同じBE Totのnative錐の脚と、元の指定BK錐の係数での照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory SSet MonoidalCategory CartesianMonoidalCategory
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open scoped Simplicial
variable (I : Type u) [SmallCategory I] (H : I ⥤ SSet.{u})

/-- 元のliftにBK切断比較を合成して評価すると、元の同じ自然変換のweighted nerve族。 -/
theorem bousfieldKanSectionsMap_lift_evaluation {A : SSet.{u}}
    (η : bousfieldKanWeight I ⊗ (Functor.const I).obj A ⟶ H) :
    (nerve I ◁ (weightedSectionsLift η ≫ bousfieldKanSectionsMap H)) ≫
      simplicialSectionsEvaluation (weightedNerveProjection H) =
        weightedNerveSectionFromTransform η := by
  rw [whiskerLeft_comp, Category.assoc, bousfieldKanSectionsMap_evaluation]
  change (nerve I ◁ weightedSectionsLift η) ≫
    weightedNerveSectionFromTransform (weightedSectionsUncurry (𝟙 _)) = _
  rw [← weightedNerveSectionFromTransform_parameter,
    ← weightedSectionsUncurry_precomp, Category.comp_id, weightedSectionsUncurry_lift]

/-- 零次のweighted nerve係数は、同じBK重みの恒等射の零単体での評価。 -/
theorem weightedNerveSectionFromTransform_zero_point
    (s : bousfieldKanWeight I ⟶ H) (i : I) :
    (weightedNerveSectionFromTransform
      (fst (bousfieldKanWeight I) ((Functor.const I).obj (Δ[0] : SSet.{u})) ≫ s)).app
        (Opposite.op ⦋0⦌) (nerveVertex i, SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) =
    (weightedNerveConstantLift H i).app (Opposite.op ⦋0⦌)
      ((s.app i).app (Opposite.op ⦋0⦌) (nerveVertex (Over.mk (𝟙 i)))) := by
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  apply NatTrans.ext
  funext j
  fin_cases j
  apply SSet.yonedaEquiv.injective
  change SSet.yonedaEquiv
    ((prefixOverParameter (nerveVertex i)
      (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))))).app (0 : Fin 1) ≫
        fst ((bousfieldKanWeight I).obj i) (Δ[0] : SSet.{u}) ≫ s.app i) =
    SSet.yonedaEquiv (stdSimplex.map (simplexPrefixInclusion 0 0 (Nat.le_refl 0)) ≫
      SSet.yonedaEquiv.symm
        ((s.app i).app (Opposite.op ⦋0⦌) (nerveVertex (Over.mk (𝟙 i)))))
  rw [Equiv.symm_apply_apply, simplexPrefixInclusion_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Equiv.apply_symm_apply]
  change SSet.yonedaEquiv
    (lift ((prefixOverWeight (nerveVertex i)).app (0 : Fin 1)) _ ≫ fst _ _ ≫ s.app i) = _
  rw [lift_fst_assoc, SSet.yonedaEquiv_comp]
  change (s.app i).app (Opposite.op ⦋0⦌)
    (SSet.yonedaEquiv (SSet.yonedaEquiv.symm (prefixOverChain (nerveVertex i) (0 : Fin 1)))) = _
  rw [Equiv.apply_symm_apply]
  apply congrArg ((s.app i).app (Opposite.op ⦋0⦌))
  exact ComposableArrows.ext₀ rfl

/-- 元の指定BK点を元の同じ係数へ戻すと、恒等射の零単体での元の値になる。 -/
theorem bousfieldKanSectionsIso_nativeWeightedPoint_fiber
    (s : bousfieldKanWeight I ⟶ H) (i : I) :
    ((weightedNerveFiberIso H i).inv.app (Opposite.op ⦋0⦌))
      ((simplicialSectionsFiberEvaluation (weightedNerveProjection H) (nerveVertex i)).app
        (Opposite.op ⦋0⦌)
        (((bousfieldKanSectionsIso H).hom.app (Opposite.op ⦋0⦌))
          (nativeWeightedPoint I s))) =
      (s.app i).app (Opposite.op ⦋0⦌) (nerveVertex (Over.mk (𝟙 i))) := by
  let η := fst (bousfieldKanWeight I) ((Functor.const I).obj (Δ[0] : SSet.{u})) ≫ s
  have h := congrArg (fun f => f.app (Opposite.op ⦋0⦌)
    (nerveVertex i, SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))))
      (bousfieldKanSectionsMap_lift_evaluation I H η)
  change (simplicialSectionsEvaluation (weightedNerveProjection H)).app (Opposite.op ⦋0⦌)
    (nerveVertex i, (bousfieldKanSectionsMap H).app (Opposite.op ⦋0⦌)
      (nativeWeightedPoint I s)) = _ at h
  have he : Function.Injective ((weightedNerveFiberIso H i).hom.app (Opposite.op ⦋0⦌)) :=
    ((isIso_iff_bijective _).mp inferInstance).injective
  apply he
  change (((weightedNerveFiberIso H i).inv ≫ (weightedNerveFiberIso H i).hom).app
    (Opposite.op ⦋0⦌)) _ = _
  rw [Iso.inv_hom_id]
  apply Subtype.ext
  change (simplicialSectionsEvaluation (weightedNerveProjection H)).app (Opposite.op ⦋0⦌)
    (nerveVertex i, (bousfieldKanSectionsMap H).app (Opposite.op ⦋0⦌)
      (nativeWeightedPoint I s)) = _
  exact h.trans (weightedNerveSectionFromTransform_zero_point I H s i)

end SerrePositivity.EInfinity.HomotopyWeight
