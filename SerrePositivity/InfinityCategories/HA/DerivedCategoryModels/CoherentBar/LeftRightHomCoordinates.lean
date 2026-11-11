module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.LeftRightHomIso
/-!
概要：左右 pinched Hom の厳密同型の全線形成分を計算する。
方針：反対模型の座標、線形反転、恒等 Hom 鎖写像の実計算則を合成する。
規約：全非空部分集合・全次数を保持する。
使われ方：標準 native 余錐の族との単体ごとの照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] (x y : C)

lemma dgCoherentBarLeftRightHomIso_linear {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLeftRightHomIso R C x y).hom.app (Opposite.op ⦋n⦌) s) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap (A := R) (D := Cᵒᵖ) (E := C)
        (x := Opposite.op y) (y := Opposite.op x) (x' := x) (y' := y)
        (𝟙 (_root_.SerrePositivity.DifferentialGraded.homObject R C x y))
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLinearReflectionSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedLinearEquiv R C x y n s)) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex (A := R) (D := Cᵒᵖ) (E := C)
    (x := Opposite.op y) (y := Opposite.op x) (x' := x) (y' := y)
    (𝟙 (_root_.SerrePositivity.DifferentialGraded.homObject R C x y))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarPinchedReflectionSimplex R Cᵒᵖ (Opposite.op y) (Opposite.op x)
      (SSet.opObjEquiv ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedOppositeIso R C x y).hom.app _ s)))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex_linear, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarPinchedReflectionSimplex_linear]
  rfl

lemma dgCoherentBarLeftRightHomIso_component {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) _⦋n⦌)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLeftRightHomIso R C x y).hom.app (Opposite.op ⦋n⦌) s)).component J k hJ hk)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLinearReflectionSign J.card •
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedLinearEquiv R C x y n s).val.component
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse J) k (hJ.image Fin.rev)
          (by simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.card_reverse] using hk)) := by
  have h := congrArg Subtype.val (dgCoherentBarLeftRightHomIso_linear R C x y s)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData _ = _ at h
  rw [h]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
