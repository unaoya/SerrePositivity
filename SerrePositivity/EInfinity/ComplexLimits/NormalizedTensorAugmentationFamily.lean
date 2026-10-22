module

public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorAugmentationIdentity
public import SerrePositivity.EInfinity.ComplexLimits.ComplexPinchedPostcomposition
public import SerrePositivity.EInfinity.ComplexLimits.ComplexClosedEdgeHomotopyEquivalence

/-!
# 元の正規化 frame の実屋根評価方程式

概要：元の augmentation の閉辺と普遍 Hom 族が互いに逆であることを証明する。
方針：全族の後合成式、元の恒等頂点との一致、実収縮による可逆性を使う。
規約：任意の複体・全次数・任意のパラメータを保つ。
使われ方：同じ U の導来単位の写像空間比較の幾何的三角形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open DGNerve
variable (A : Type u) [CommRing A]

lemma normalizedTensorUniversalSimplex_augmentation_family (X : Complex A)
    (n : SimplexCategory) (K : SSet.{u + 1})
    (t : K ⟶ SSet.uliftFunctor.{u + 1, u}.obj (SSet.stdSimplex.obj n)) :
    dgPinchedFamilyHom A (Complex A) (t ≫ normalizedTensorUniversalSimplex A X n) ≫
      constantFunctorHomMap K (Truncated.HomotopyCategory.homMk
        (V := (truncation 2).obj (dgNerve A (Complex A)))
        (dgClosedEdge A (Complex A)
          ((complexToClosed A).map ((normalizedSimplexTensorAugmentation A X).app n)))) =
    𝟙 _ := by
  rw [← complexPinchedPostcomposition_family, Category.assoc,
    normalizedTensorUniversalSimplex_augmentation_identity, SSet.comp_const]
  have h : dgPinchedFamilyHom A (Complex A) (SSet.const (X := K)
      (pinchedClosedVertex A (Complex A) ((complexToClosed A).map (𝟙 X)))) =
    constantFunctorHomMap K (Truncated.HomotopyCategory.homMk
        (V := (truncation 2).obj (dgNerve A (Complex A)))
      (dgClosedEdge A (Complex A) ((complexToClosed A).map (𝟙 X)))) :=
    pinchedFamilyHom_const_vertex (X := dgNerve A (Complex A)) _
  rw [h, complexToClosed_edge_id]
  have hi := Truncated.HomotopyCategory.homMk_id
    (V := (truncation 2).obj (dgNerve A (Complex A))) (Simplex.vertex X)
  exact (congrArg (constantFunctorHomMap K) hi).trans
    (constantFunctorHomMap_id (X := dgNerve A (Complex A)) K (Simplex.vertex X))

lemma normalizedTensorUniversalSimplex_augmentation_inverse (X : Complex A)
    (n : SimplexCategory) (K : SSet.{u + 1})
    (t : K ⟶ SSet.uliftFunctor.{u + 1, u}.obj (SSet.stdSimplex.obj n)) :
    constantFunctorHomMap K (Truncated.HomotopyCategory.homMk
        (V := (truncation 2).obj (dgNerve A (Complex A)))
        (dgClosedEdge A (Complex A)
          ((complexToClosed A).map ((normalizedSimplexTensorAugmentation A X).app n)))) ≫
      dgPinchedFamilyHom A (Complex A) (t ≫ normalizedTensorUniversalSimplex A X n) =
    𝟙 _ := by
  have : IsInvertibleEdge (X := dgNerve A (Complex A)) (dgClosedEdge A (Complex A)
      ((complexToClosed A).map ((normalizedSimplexTensorAugmentation A X).app n))) :=
    normalizedTensorAugmentation_edge_invertible A X n
  have : IsIso (constantFunctorHomMap K (Truncated.HomotopyCategory.homMk
        (V := (truncation 2).obj (dgNerve A (Complex A)))
      (dgClosedEdge A (Complex A)
        ((complexToClosed A).map ((normalizedSimplexTensorAugmentation A X).app n))))) := by
    dsimp only [constantFunctorHomMap]
    infer_instance
  let a := constantFunctorHomMap K (Truncated.HomotopyCategory.homMk
    (V := (truncation 2).obj (dgNerve A (Complex A))) (dgClosedEdge A (Complex A)
      ((complexToClosed A).map ((normalizedSimplexTensorAugmentation A X).app n))))
  let b := dgPinchedFamilyHom A (Complex A) (t ≫ normalizedTensorUniversalSimplex A X n)
  have h : b ≫ a = 𝟙 _ := normalizedTensorUniversalSimplex_augmentation_family A X n K t
  change a ≫ b = 𝟙 _
  apply (cancel_mono a).1
  calc
    (a ≫ b) ≫ a = a ≫ (b ≫ a) := Category.assoc _ _ _
    _ = a ≫ 𝟙 _ := congrArg (fun f => a ≫ f) h
    _ = 𝟙 _ ≫ a := by simp

end SerrePositivity.EInfinity.ComplexLimits
