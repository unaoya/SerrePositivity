module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleSeparatedDirectEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleSeparatedMiddleCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TrianglePathInterval
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QCatCorePostcomposition

/-!
概要：全族の各入力点で、分離した長 Hom が元の全 native 区間を回収する。
方針：K・L の定値単体では二切断座標が同じ点へ戻るので、延長の対角式を使う。
規約：native 区間の全ての次数を保持する。
使われ方：再構成族の各 k における full native Hom の厳密回収。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

lemma triangleMiddleMap_identity :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePathMiddleMap.{u} (OrderHom.id : Fin 3 →o Fin 3) 0 2 = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleNativePathIntervalIso.hom := by
  classical
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro P
  apply stdSimplex.ext
  intro l
  let R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u} := P.obj l
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePathMiddle (OrderHom.id : Fin 3 →o Fin 3) R = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePathToInterval R).down
  simp [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePathMiddle, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePathToInterval]

lemma triangleLiftedCoordinate_constant {A : SSet.{u}} {K : SSet.{max u v}} {n : ℕ}
    (c : A ⟶ (Δ[n] : SSet.{u})) (k : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLiftedCoordinate c (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant k n) = SSet.const k := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLiftedCoordinate, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.yonedaEquiv_symm_pinchedConstant]
  simp only [Category.assoc, SSet.comp_const]

lemma triangleSeparatedLongHom_constant
    {K L : SSet.{max u v}} {H : SSet.{u}}
    (M : (Δ[1] : SSet.{max u v}) ⊗ ((K ⊗ K) ⊗ L) ⟶ (SSet.uliftFunctor.{v, u}).obj H)
    (q : (Δ[1] : SSet.{max u v}) ⊗ (K ⊗ L) ⟶ (SSet.uliftFunctor.{v, u}).obj H)
    (hdiag : (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleParameterDiagonal K L) ≫ M = q)
    (k : K _⦋0⦌) (l : L _⦋0⦌) {n : ℕ} (t : Fin (n + 1) →o Fin 3)
    {i : Fin (n + 1)} (hi : t i = 0) (j : Fin (n + 1)) :
    (SSet.uliftFunctor.{v, u}).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedLongHom M (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant k n) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant l n) t hi j) =
      lift ((SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePathMiddleMap t i j) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} 1).hom) (SSet.const (k, l)) ≫ q := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedLongHom_map, triangleLiftedCoordinate_constant,
    triangleLiftedCoordinate_constant, triangleLiftedCoordinate_constant, ← hdiag]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
