module

public import SerrePositivity.InfinityCategories.F1.Diagrams.TriangleSeparatedDirectEvaluation
public import SerrePositivity.InfinityCategories.F1.Diagrams.TriangleSeparatedMiddleCoordinates
public import SerrePositivity.InfinityCategories.F1.Diagrams.TrianglePathInterval
public import SerrePositivity.InfinityCategories.F1.Categories.QCatCorePostcomposition

/-!
概要：全族の各入力点で、分離した長 Hom が元の全 native 区間を回収する。
方針：K・L の定値単体では二切断座標が同じ点へ戻るので、延長の対角式を使う。
規約：native 区間の全ての次数を保持する。
使われ方：再構成族の各 k における full native Hom の厳密回収。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma triangleMiddleMap_identity :
    trianglePathMiddleMap.{u} (OrderHom.id : Fin 3 →o Fin 3) 0 2 = triangleNativePathIntervalIso.hom := by
  classical
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro P
  apply stdSimplex.ext
  intro l
  let R : TriangleNativePath.{u} := P.obj l
  change trianglePathMiddle (OrderHom.id : Fin 3 →o Fin 3) R = (trianglePathToInterval R).down
  simp [trianglePathMiddle, trianglePathToInterval]

lemma triangleLiftedCoordinate_constant {A : SSet.{u}} {K : SSet.{max u v}} {n : ℕ}
    (c : A ⟶ (Δ[n] : SSet.{u})) (k : K _⦋0⦌) :
    triangleLiftedCoordinate c (PinchedHom.constant k n) = SSet.const k := by
  rw [triangleLiftedCoordinate, yonedaEquiv_symm_pinchedConstant]
  simp only [Category.assoc, SSet.comp_const]

lemma triangleSeparatedLongHom_constant
    {K L : SSet.{max u v}} {H : SSet.{u}}
    (M : (Δ[1] : SSet.{max u v}) ⊗ ((K ⊗ K) ⊗ L) ⟶ (SSet.uliftFunctor.{v, u}).obj H)
    (q : (Δ[1] : SSet.{max u v}) ⊗ (K ⊗ L) ⟶ (SSet.uliftFunctor.{v, u}).obj H)
    (hdiag : (Δ[1] ◁ triangleParameterDiagonal K L) ≫ M = q)
    (k : K _⦋0⦌) (l : L _⦋0⦌) {n : ℕ} (t : Fin (n + 1) →o Fin 3)
    {i : Fin (n + 1)} (hi : t i = 0) (j : Fin (n + 1)) :
    (SSet.uliftFunctor.{v, u}).map
      (triangleSeparatedLongHom M (PinchedHom.constant k n) (PinchedHom.constant l n) t hi j) =
      lift ((SSet.uliftFunctor.{v, u}).map (trianglePathMiddleMap t i j) ≫
        (HomotopyLimits.uliftStdSimplexIso.{u, v} 1).hom) (SSet.const (k, l)) ≫ q := by
  rw [triangleSeparatedLongHom_map, triangleLiftedCoordinate_constant,
    triangleLiftedCoordinate_constant, triangleLiftedCoordinate_constant, ← hdiag]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  rfl

end SerrePositivity.InfinityCategories
