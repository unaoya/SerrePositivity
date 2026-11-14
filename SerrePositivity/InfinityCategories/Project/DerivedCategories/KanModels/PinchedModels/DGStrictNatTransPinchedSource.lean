module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.DGStrictNatTransPinchedSlice

/-! # 固定標的の自然変換 prism の始域射影

概要：slice prism の始域は、係数を忘れた自然変換の始対象成分の辺で決まる。
方針：prism の前面への制限を自然変換の引き戻し自然性で計算する。
規約：全次数の写像の等式。使われ方：実分母の辺を保つ屋根 pullback への持ち上げ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet MonoidalCategory
open CartesianMonoidalCategory
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (C D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A C] [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
variable {F G : DGFunctor A C D} (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (x y : C)

/-- 自然変換の指定対象における辺を、単体的写像として読む。 -/
def dgStrictNatTransPointMap : (Δ[1] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D :=
  lift (SSet.const (Y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A C) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) (𝟙 Δ[1]) ≫ η.homotopyMap

/-- slice の指定単体の始域は、元の係数単体の前面を二相で写した単体。 -/
lemma dgStrictNatTransPinchedSliceSimplex_projection {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A C x y) _⦋n⦌) (β : Fin (n + 1) →o Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _).app (Opposite.op ⦋n⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPinchedSliceSimplex A C D η x y s β) =
      η.simplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A C) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) n) β := by
  let t := η.simplex s.val (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase β)
  have hp : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _).app (Opposite.op ⦋n⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPinchedSliceSimplex A C D η x y s β) =
      t.pullback Fin.castSuccOrderEmb.toOrderHom := by
    change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[n] Δ[0] ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm t)) = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinStdSimplexIso_rightPoint_inl,
      SSet.yonedaEquiv_symm_naturality_left, Equiv.apply_symm_apply]
    rfl
  have hs : s.val.pullback Fin.castSuccOrderEmb.toOrderHom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A C) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) n := s.source
  have ht := (η.simplex_pullback s.val (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase β)
    Fin.castSuccOrderEmb.toOrderHom).symm
  exact hp.trans (ht.trans
    ((congrArg (η.simplex (s.val.pullback Fin.castSuccOrderEmb.toOrderHom))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase_front β)).trans (congrArg (fun t => η.simplex t β) hs)))

/-- slice prism の始域への射影は、係数を忘れた始点の自然変換の辺。 -/
lemma dgStrictNatTransPinchedSlice_projection :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPinchedSlice A C D η x y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _ =
      snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A C x y) Δ[1] ≫ dgStrictNatTransPointMap A C D η x := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  exact dgStrictNatTransPinchedSliceSimplex_projection A C D η x y s.1
    (SSet.stdSimplex.objEquiv s.2).toOrderHom

end SerrePositivity.InfinityCategories.Project.DerivedCategories
