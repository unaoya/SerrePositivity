module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.CoherentCoconeLegs
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.StrictNativeCocones

/-!
概要：通常の余錐の native な表示の脚を元の通常の射と同定する。
方針：添字と値域の反転を脚の等式で追跡し、反対の錐の脚の計算を用いる。
規約：区間からの実際の単体的写像の等号で主張する。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）、𝒮 の余積の包含射の同定。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
noncomputable section
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 概要：反対の通常の射の coherent 表示を区間と値域で反転すると元の射になる。
方針：coherent nerve の帰還の同型を一次単体で展開し、豊穣関手の対象と Hom を比較する。
規約：単体的圏の Hom の Kan 性は要求しない。
使われ方：Kerodon 4.6.7（Tag 01LA）・7.5.4.6（Tag 03BB）、元の余錐の脚への帰還。 -/
lemma coherentOppositeReturnIso_hom_edge {x y : C} (f : x ⟶ y) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentOppositeReturnIso C).hom.app (Opposite.op ⦋1⦌)
        (SSet.opObjEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent Cᵒᵖ).app (Opposite.op ⦋1⦌)
          (ComposableArrows.mk₁ f.op))) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f) := by
  change (SSet.opFunctorCompOpFunctorIso.app (SimplicialNerve C)).hom.app _
    ((SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveOppositeIso C).inv).app _
      (SSet.opObjEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent Cᵒᵖ).app (Opposite.op ⦋1⦌)
        (ComposableArrows.mk₁ f.op)))) = _
  rw [SSet.opFunctor_map, Equiv.apply_symm_apply]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentOppositeInverseSimplex
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent Cᵒᵖ).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f.op)) = _
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
使われ方：Kerodon 7.5.4.6（Tag 03BB）、strict な余錐の成分の整合性。 -/
def strictNativeCoconeLeg {F : I ⥤ C} (c : Cocone F) (i : I) :
    (Δ[1] : SSet.{max u v}) ⟶ SimplicialNerve C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentCoconeLegMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone c)
    (SSet.yonedaEquiv.symm (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)))

/-- 概要：通常の余錐の native な表示の各脚は元の余錐の射の coherent 表示。
方針：脚の反転の等式を元の錐の脚の計算に適用し、値域の反転を戻す。
規約：元の射 c.ι.app i との区間からの写像の厳密な等式。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）、実際の ∞ 余積の包含の同定。 -/
lemma strictNativeCoconeLeg_eq {F : I ⥤ C} (c : Cocone F) (i : I) :
    strictNativeCoconeLeg c i = SSet.yonedaEquiv.symm
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ (c.ι.app i))) := by
  let p : (Δ[0] : SSet.{max u v}) ⟶ (SSet.uliftFunctor.{v, u}).obj (nerve I) :=
    SSet.yonedaEquiv.symm (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i))
  let q : (Δ[0] : SSet.{max u v}) ⟶ (SSet.uliftFunctor.{v, u}).obj (nerve Iᵒᵖ) :=
    SSet.yonedaEquiv.symm (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Opposite.op i)))
  have hp : p ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictCoconeIndexIso.{u, v} I).hom =
      (stdSimplex.opIso ⦋0⦌).inv ≫ SSet.opFunctor.map q := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableReverseSimplex_yoneda]
    change (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictCoconeIndexIso.{u, v} I).hom.app _
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)) = SSet.opObjEquiv.symm (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Opposite.op i)))
    exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictCoconeIndexIso_hom_vertex i
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentCoconeLegMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone c) p = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentCoconeLegMap_ofDiagramEq, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCocone,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentCoconeLegMap_post, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentCoconeLegMap_restrict, hp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentCoconeLegMap_reverse]
  change ((stdSimplex.opIso ⦋1⦌).inv ≫
    SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentConeLeg c.op (Opposite.op i))) ≫ _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentConeLeg_eq]
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableReverseSimplex_yoneda, Equiv.apply_symm_apply]
  exact coherentOppositeReturnIso_hom_edge _

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
