module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.DGWalkingHomPinched
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGWalkingHomPrismZero
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.DGStrictNatTransPinchedSlice
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGStrictNatTransPointEdge

/-! # 閉前合成の全次数の固定標的 slice prism

概要：閉前合成した係数の標準 slice 表示と元の係数の表示を実ホモトピーで結ぶ。
方針：自由 Hom の厳密自然変換の prism に元の全係数単体を含め、両端を回収する。
規約：全ての面・退化と両端を厳密に保つ。使われ方：実屋根の細分輸送への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet MonoidalCategory CartesianMonoidalCategory
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {p q : D} (y : D)
variable (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q)

/-- 元の pinched Hom 全体に対する、閉前合成の指定標的 slice 内の実 prism。 -/
def dgClosedPrecompositionSlicePrism :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D q y ⊗ (Δ[1] : SSet.{max u v}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPinched A D q y ▷ Δ[1]) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPinchedSlice A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHom.{u, v} A (homObject A D q y)) D
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPrecomposeNatTrans A D y r)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomSource A (homObject A D q y))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomTarget A (homObject A D q y))

/-- 実 slice prism の零端点は、指定閉射の全次数の前合成による像。 -/
lemma dgClosedPrecompositionSlicePrism_zero :
    SSet.ι₀ ≫ dgClosedPrecompositionSlicePrism A D y r =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A D r ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomSliceFiberIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex p) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
          ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex p) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPrecomposeNatTrans A D y r).simplex
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPinched A D q y).app (Opposite.op ⦋n⦌) s).val
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase (OrderHom.const (Fin (n + 1)) (0 : Fin 2)))) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A D r).app (Opposite.op ⦋n⦌) s).val)
  exact congrArg (fun t => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫
    (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm t)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPrism_zero A D y r _).trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPinched_evaluation_val A D D q y p y (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D r) s))

/-- 実 slice prism の一端点は、元の全係数の標準 slice 表示。 -/
lemma dgClosedPrecompositionSlicePrism_one :
    SSet.ι₁ ≫ dgClosedPrecompositionSlicePrism A D y r =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomSliceFiberIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex q) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
        ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex q) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  let c := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPinched A D q y).app (Opposite.op ⦋n⦌) s
  let η := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPrecomposeNatTrans A D y r
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
    (η.simplex c.val (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase (OrderHom.const (Fin (n + 1)) (1 : Fin 2)))) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm s.val
  have h := (congrArg (η.simplex c.val) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase_one n)).trans (η.simplex_one c.val)
  have hval : c.val.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomOriginalEvaluation A D q y) = s.val := by
    have h' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPinched_evaluation_val A D D q y q y (𝟙 _) s
    have hid := congrArg (fun f => (f.app (Opposite.op ⦋n⦌) s).val)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_id (A := A) (D := D) (x := q) (y := y))
    exact h'.trans hid
  exact congrArg (fun t => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫
    (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm t) (h.trans hval)

/-- 閉前合成 prism の始域は、元の指定閉射の実辺に沿って動く。 -/
lemma dgClosedPrecompositionSlicePrism_source :
    dgClosedPrecompositionSlicePrism A D y r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _ =
      snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D q y) Δ[1] ≫
        (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D r).edge := by
  let η := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPrecomposeNatTrans A D y r
  let j := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomPinched A D q y
  let f := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPointMap A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHom.{u, v} A (homObject A D q y)) D η
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomSource A (homObject A D q y))
  have h := congrArg (fun k => (j ▷ (Δ[1] : SSet.{max u v})) ≫ k)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPinchedSlice_projection A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHom.{u, v} A (homObject A D q y)) D η
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomSource A (homObject A D q y))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomTarget A (homObject A D q y)))
  calc
    _ = (j ▷ Δ[1]) ≫ snd _ Δ[1] ≫ f := by
      exact (Category.assoc _ _ _).trans h
    _ = snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D q y) Δ[1] ≫ f := by
      rw [← Category.assoc, whiskerRight_snd]
    _ = _ := congrArg (fun f => snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D q y) Δ[1] ≫ f)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPointMap_edge A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHom.{u, v} A (homObject A D q y)) D η
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomSource A (homObject A D q y)))


end SerrePositivity.InfinityCategories.Project.DerivedCategories
