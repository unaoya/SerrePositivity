module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeCoordinates
/-!
概要：任意の native 余錐から取り出す単体は、元の全単調写像に自然である。
方針：標準単体と点の join 同型の自然性と、余錐の単体写像を使う。
規約：余錐の普遍性を仮定しない。
使われ方：逆向きの成分族の退化消滅と HA 方程式の回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarCoconeSimplex_map (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) {m n : ℕ} (s : I _⦋n⦌)
    (α : Fin (m + 1) →o Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSimplex R D F c (I.map (SimplexCategory.mkHom α).op s) =
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSimplex R D F c s).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α) := by
  let A := (SSet.uliftFunctor.{max (u + 1) v, u}).obj I
  let f : (Δ[n] : SSet.{max (u + 1) v}) ⟶ A :=
    (SSet.yonedaEquiv (X := A)).symm (ULift.up s)
  have he : (SSet.yonedaEquiv (X := A)).symm
      (ULift.up (I.map (SimplexCategory.mkHom α).op s)) =
      SSet.stdSimplex.map (SimplexCategory.mkHom α) ≫ f :=
    (SSet.yonedaEquiv_symm_naturality_left (SimplexCategory.mkHom α) (X := A)
      (ULift.up s)).symm
  have hi : SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend (SimplexCategory.mkHom α)) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{max (u + 1) v} n 0).inv =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{max (u + 1) v} m 0).inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.map (SimplexCategory.mkHom α)) (𝟙 Δ[0]) := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{max (u + 1) v} n 0).hom).1
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinStdSimplexIso_rightPoint_naturality, Iso.inv_hom_id_assoc]
  have hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.map (SimplexCategory.mkHom α) ≫ f) (𝟙 Δ[0]) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.map (SimplexCategory.mkHom α)) (𝟙 Δ[0]) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Δ[0]) := by
    simpa only [Category.id_comp] using
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp (SSet.stdSimplex.map (SimplexCategory.mkHom α)) f (𝟙 Δ[0]) (𝟙 Δ[0])
  change (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D)))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{max (u + 1) v} m 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap
        ((SSet.yonedaEquiv (X := A)).symm
          (ULift.up (I.map (SimplexCategory.mkHom α).op s))) (𝟙 Δ[0]) ≫ c.val) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend (SimplexCategory.mkHom α)).op
      ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D)))
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{max (u + 1) v} n 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Δ[0]) ≫ c.val))
  rw [he, hj, SSet.yonedaEquiv_naturality]
  simp only [← Category.assoc, hi]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
