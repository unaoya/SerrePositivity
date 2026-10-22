module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorRoofEvaluation
public import SerrePositivity.EInfinity.ComplexLimits.IntervalFamilyFunctorTriangle

/-!
概要：元の正規化単体の実屋根評価は同じ関手 F の像でも成立する。
方針：元の全族方程式を全区間族の後作用で送る。
規約：任意の複体・次数・パラメータ・同じ射を保持する。
使われ方：元の半自由分解による既存 D(R) の幾何的評価三角形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories DGNerve
variable (A : Type u) [CommRing A]

lemma normalizedTensorRoofEvaluation_family_map {C : SSet.{u + 1}}
    (F : dgNerve A (Complex A) ⟶ C) (X Y : Complex A) (n : SimplexCategory)
    (g : (normalizedSimplexTensor A X).obj n ⟶ Y) (K : SSet.{u + 1})
    (t : K ⟶ SSet.uliftFunctor.{u + 1, u}.obj (SSet.stdSimplex.obj n)) :
    constantFunctorHomMap K ((hoFunctor.map F).toFunctor.map
      (Truncated.HomotopyCategory.homMk
        (V := (truncation 2).obj (dgNerve A (Complex A)))
        (dgClosedEdge A (Complex A)
          ((complexToClosed A).map ((normalizedSimplexTensorAugmentation A X).app n))))) ≫
      intervalFamilyHom (t ≫ normalizedTensorHomPinchedSimplex A X Y n g ≫
        pinchedHomToIntervalMappingSpace (X := dgNerve A (Complex A))
          (Simplex.vertex X) (Simplex.vertex Y) ≫
        intervalFunctorMap F (Simplex.vertex X) (Simplex.vertex Y)) =
    constantFunctorHomMap K ((hoFunctor.map F).toFunctor.map
      (Truncated.HomotopyCategory.homMk
        (V := (truncation 2).obj (dgNerve A (Complex A)))
        (dgClosedEdge A (Complex A) ((complexToClosed A).map g)))) := by
  let a := Truncated.HomotopyCategory.homMk
    (V := (truncation 2).obj (dgNerve A (Complex A))) (dgClosedEdge A (Complex A)
      ((complexToClosed A).map ((normalizedSimplexTensorAugmentation A X).app n)))
  let b := Truncated.HomotopyCategory.homMk
    (V := (truncation 2).obj (dgNerve A (Complex A)))
    (dgClosedEdge A (Complex A) ((complexToClosed A).map g))
  let f : K ⟶ intervalMappingSpace (X := dgNerve A (Complex A))
      (Simplex.vertex X) (Simplex.vertex Y) :=
    (t ≫ normalizedTensorHomPinchedSimplex A X Y n g) ≫
      pinchedHomToIntervalMappingSpace (X := dgNerve A (Complex A)) _ _
  have h : constantFunctorHomMap K a ≫ intervalFamilyHom f = constantFunctorHomMap K b :=
    normalizedTensorRoofEvaluation_family A X Y n g K t
  exact intervalFamilyFunctorMap_triangle F a b f h

end SerrePositivity.EInfinity.ComplexLimits
