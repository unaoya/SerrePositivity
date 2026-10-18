module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentCoconeLegs
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictNativeCocones

/-!
概要：通常の余錐の native な表示の脚を元の通常の射と同定する。
方針：添字と値域の反転を脚の等式で追跡し、反対の錐の脚の計算を用いる。
規約：区間からの実際の単体的写像の等号で主張する。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6、𝒮 の余積の包含射の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 概要：反対の通常の射の coherent 表示を区間と値域で反転すると元の射になる。
方針：coherent nerve の帰還の同型を一次単体で展開し、豊穣関手の対象と Hom を比較する。
規約：単体的圏の Hom の Kan 性は要求しない。
使われ方：Kerodon 4.6.7・7.5.4.6、元の余錐の脚への帰還。 -/
lemma coherentOppositeReturnIso_hom_edge {x y : C} (f : x ⟶ y) :
    (coherentOppositeReturnIso C).hom.app (Opposite.op ⦋1⦌)
        (SSet.opObjEquiv.symm ((nerveToCoherent Cᵒᵖ).app (Opposite.op ⦋1⦌)
          (ComposableArrows.mk₁ f.op))) =
      (nerveToCoherent C).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f) := by
  change (SSet.opFunctorCompOpFunctorIso.app (SimplicialNerve C)).hom.app _
    ((SSet.opFunctor.map (coherentNerveOppositeIso C).inv).app _
      (SSet.opObjEquiv.symm ((nerveToCoherent Cᵒᵖ).app (Opposite.op ⦋1⦌)
        (ComposableArrows.mk₁ f.op)))) = _
  rw [SSet.opFunctor_map, Equiv.apply_symm_apply]
  change coherentOppositeInverseSimplex
    ((nerveToCoherent Cᵒᵖ).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f.op)) = _
  refine EnrichedFunctor.ext SSet ?_ ?_
  · rintro ⟨i⟩
    fin_cases i <;> rfl
  · rintro ⟨i⟩ ⟨j⟩
    fin_cases i <;> fin_cases j <;> simp only [eqToHom_refl, Category.comp_id]
    all_goals first
    | rfl
    | apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro s
      have h := SimplicialThickening.Path.le (s.obj 0)
      change (1 : Fin 2) ≤ 0 at h
      omega

/-- 概要：元の標準図式上の通常の余錐の指定した脚。
方針：添字の標準頂点で native な余錐の脚の写像を取る。
規約：頂点は nerve の明示的な ULift に置く。
使われ方：Kerodon 7.5.4.6、strict な余錐の成分の整合性。 -/
def strictNativeCoconeLeg {F : I ⥤ C} (c : Cocone F) (i : I) :
    (Δ[1] : SSet.{max u v}) ⟶ SimplicialNerve C :=
  coherentCoconeLegMap (strictNativeCocone c)
    (SSet.yonedaEquiv.symm (ULift.up (nerveVertex i)))

/-- 概要：通常の余錐の native な表示の各脚は元の余錐の射の coherent 表示。
方針：脚の反転の等式を元の錐の脚の計算に適用し、値域の反転を戻す。
規約：元の射 c.ι.app i との区間からの写像の厳密な等式。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6、実際の ∞ 余積の包含の同定。 -/
lemma strictNativeCoconeLeg_eq {F : I ⥤ C} (c : Cocone F) (i : I) :
    strictNativeCoconeLeg c i = SSet.yonedaEquiv.symm
      ((nerveToCoherent C).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ (c.ι.app i))) := by
  let p : (Δ[0] : SSet.{max u v}) ⟶ (SSet.uliftFunctor.{v, u}).obj (nerve I) :=
    SSet.yonedaEquiv.symm (ULift.up (nerveVertex i))
  let q : (Δ[0] : SSet.{max u v}) ⟶ (SSet.uliftFunctor.{v, u}).obj (nerve Iᵒᵖ) :=
    SSet.yonedaEquiv.symm (ULift.up (nerveVertex (Opposite.op i)))
  have hp : p ≫ (strictCoconeIndexIso.{u, v} I).hom =
      (stdSimplex.opIso ⦋0⦌).inv ≫ SSet.opFunctor.map q := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, stableReverseSimplex_yoneda]
    change (strictCoconeIndexIso.{u, v} I).hom.app _
      (ULift.up (nerveVertex i)) = SSet.opObjEquiv.symm (ULift.up (nerveVertex (Opposite.op i)))
    exact strictCoconeIndexIso_hom_vertex i
  change coherentCoconeLegMap (strictNativeCocone c) p = _
  rw [strictNativeCocone, coherentCoconeLegMap_ofDiagramEq, strictCoherentCocone,
    coherentCoconeLegMap_post, coherentCoconeLegMap_restrict, hp,
    coherentCoconeLegMap_reverse]
  change ((stdSimplex.opIso ⦋1⦌).inv ≫
    SSet.opFunctor.map (strictCoherentConeLeg c.op (Opposite.op i))) ≫ _ = _
  rw [strictCoherentConeLeg_eq]
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, stableReverseSimplex_yoneda, Equiv.apply_symm_apply]
  exact coherentOppositeReturnIso_hom_edge _

end
end SerrePositivity.InfinityCategories.HomotopyLimits
