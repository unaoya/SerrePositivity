module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedPrismPhase
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedSlice
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NatTrans
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedComponents

/-! # 厳密 dg 自然変換の固定標的 slice prism

概要：元の pinched Hom の全単体と時刻から、終点を固定した実 slice の単体を作る。
方針：前面の時刻を最終相一へ延長し、厳密自然変換の単体へ適用する。
規約：全ての面・退化に自然。使われ方：閉前合成の実屋根への全次数の移行。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet MonoidalCategory
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (C D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A C] [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
variable {F G : _root_.SerrePositivity.DifferentialGraded.DGFunctor A C D} (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (x y : C)

/-- 係数単体と時刻から、最後の標的を G(y) に固定した実 slice 単体を得る。 -/
def dgStrictNatTransPinchedSliceSimplex {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A C x y) _⦋n⦌) (β : Fin (n + 1) →o Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (G.obj y)))) _⦋n⦌ :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
    (η.simplex s.val (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase β)), by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinStdSimplexIso_rightPoint_inr,
      SSet.yonedaEquiv_symm_naturality_left]
    apply SSet.yonedaEquiv.injective
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A D).injective
    change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans.phaseObj F G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase β (Fin.last (n + 1)))
      (s.val.obj (Fin.last (n + 1))) = G.obj y
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase_last, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.target_obj s]
    rfl⟩

/-- 全係数と全時刻を持つ、指定終点の実 slice への単体的 prism。 -/
def dgStrictNatTransPinchedSlice : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A C x y ⊗ (Δ[1] : SSet.{max u v}) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (G.obj y))) where
  app _ := ↾fun s => dgStrictNatTransPinchedSliceSimplex A C D η x y s.1
    (SSet.stdSimplex.objEquiv s.2).toOrderHom
  naturality {n m} α := by
    obtain ⟨⟨n⟩⟩ := n
    obtain ⟨⟨m⟩⟩ := m
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    let β := (SSet.stdSimplex.objEquiv s.2).toOrderHom
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso m 0).hom ≫ (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
      (η.simplex (s.1.val.pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α.unop).toOrderHom)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase (β.comp α.unop.toOrderHom))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.map α.unop) (𝟙 Δ[0]) ≫
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
          (η.simplex s.1.val (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase β)))
    let t := η.simplex s.1.val (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase β)
    have ht : η.simplex (s.1.val.pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α.unop).toOrderHom)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase (β.comp α.unop.toOrderHom)) =
        t.pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α.unop).toOrderHom :=
      (congrArg (η.simplex (s.1.val.pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α.unop).toOrderHom))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase_comp β α.unop.toOrderHom)).trans
          (η.simplex_pullback s.1.val (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase β)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α.unop).toOrderHom)
    refine (congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D (m + 1) => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso m 0).hom ≫
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm t) ht).trans ?_
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso m 0).hom ≫ (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α.unop).op t) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.map α.unop) (𝟙 Δ[0]) ≫
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm t)
    rw [← SSet.yonedaEquiv_symm_naturality_left, ← Category.assoc]
    exact congrArg (fun f => f ≫ (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm t)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinStdSimplexIso_rightPoint_naturality α.unop).symm


end SerrePositivity.InfinityCategories.Project.DerivedCategories
