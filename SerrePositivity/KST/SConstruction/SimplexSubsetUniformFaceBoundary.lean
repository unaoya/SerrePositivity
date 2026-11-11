module
public import SerrePositivity.KST.SConstruction.CubicalLambdaNativeCoordinateBoundary
public import SerrePositivity.KST.SConstruction.SerreCubeFaceTopDimension

/-! # 元の HA 全面和の統一した面始域次元
概要：元の各削除部分集合の面像を、元の全体濃度から三を除いた一つの次元で読む。
方針：元の内部点削除の濃度と、元の座標同値の逆律を使う。
規約：元の標準面・出力次数・実 dg Hom 射を保持。使われ方：全面微分との直接比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped BigOperators
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の全体部分集合の同じ cube の標準面像を、全て統一した面始域次元で読む。 -/
def simplexSubsetUniformFaceTopImage {n : ℕ} (b : Bool)
    (F : DGFunctor A (CubicalLambda A (Δ[n] : SSet.{u})) D)
    (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) (h3 : 3 ≤ I.card) (i : Fin (I.card - 2)) :
    (homObject A D
      (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))))
      (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))))).X
        ((2 - (I.card : ℤ)) + 1) :=
  eqToHom (congrArg (fun k => (homObject A D
    (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))))
    (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))))).X k)
    (show -((I.card - 3 : ℕ) : ℤ) = (2 - (I.card : ℤ)) + 1 by omega))
    (serreCubeTopCellImage A _ (I.card - 3)
      (((serreCubeFace A b (I.card - 3) (Fin.cast (by omega) i)).hom ≫
        (serreConcreteCubeComplexFunctor A).map
          (concreteCubeDimensionIso (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (I.card - 2))
            (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (I.card - 3 + 1))
            (by change I.card - 2 = I.card - 3 + 1; omega)).inv ≫
          simplexSubsetLambdaCell A I hI) ≫
        F.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)))
          (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)))))

/-- 元の各内部点の標準面像は、元の全体濃度による統一した同じ面像そのもの。 -/
lemma simplexSubsetMappedFaceTopImage_uniform {n : ℕ} (b : Bool)
    (F : DGFunctor A (CubicalLambda A (Δ[n] : SSet.{u})) D)
    (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) (h3 : 3 ≤ I.card)
    (j : Fin (n + 1)) (hj : j ∈ I)
    (hjm : I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) < j)
    (hjM : j < I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) :
    simplexSubsetMappedFaceTopImage A b F I hI j hj hjm hjM =
      simplexSubsetUniformFaceTopImage A b F I hI h3
        (simplexSubsetEraseNormalizedCoordinate I hI j hj hjm hjM) := by
  have hE := simplexSubsetErase_two I hI j hjm hjM
  have hc := Finset.card_erase_add_one hj
  exact serreCubeFaceTopImage_dimension_post A b
    (m := (I.erase j).card - 2) (n := I.card - 3) (d := I.card - 2) (by omega)
    (simplexSubsetErase_normalized_codimension I hI j hj hjm hjM) (by omega)
    (simplexSubsetEraseNormalizedCoordinate I hI j hj hjm hjM)
    ((2 - (I.card : ℤ)) + 1) (by omega) (by omega)
    (simplexSubsetLambdaCell A I hI) (F.map _ _)

/-- 元の native HA の右辺は、統一した始域次元の元の標準両面像の符号付き差の全面和。 -/
lemma cubicalLambdaNativeSimplexData_rhs_uniform_faces {n : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[n] : SSet.{u})) D)
    (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) (h3 : 3 ≤ I.card) :
    (cubicalLambdaNativeSimplexData A F).rhs I
        (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
        (2 - (I.card : ℤ)) hI rfl rfl rfl =
      ∑ i : Fin (I.card - 2), ((i.val : ℤ) + 1).negOnePow •
        (simplexSubsetUniformFaceTopImage A false F I hI h3 i -
          simplexSubsetUniformFaceTopImage A true F I hI h3 i) := by
  exact (cubicalLambdaNativeSimplexData_rhs_faces A F I hI).trans
    (Finset.sum_congr rfl (fun i _ => by
      let j := simplexSubsetInteriorCoordinateEquiv I hI i
      have he : simplexSubsetEraseNormalizedCoordinate I hI j.val j.property.1
          j.property.2.1 j.property.2.2 = i :=
        (simplexSubsetInteriorCoordinateEquiv I hI).left_inv i
      exact (congrArg₂ (fun f g => ((i.val : ℤ) + 1).negOnePow • (f - g))
        (simplexSubsetMappedFaceTopImage_uniform A false F I hI h3
          j.val j.property.1 j.property.2.1 j.property.2.2)
        (simplexSubsetMappedFaceTopImage_uniform A true F I hI h3
          j.val j.property.1 j.property.2.1 j.property.2.2)).trans
        (congrArg (fun k => ((i.val : ℤ) + 1).negOnePow •
          (simplexSubsetUniformFaceTopImage A false F I hI h3 k -
            simplexSubsetUniformFaceTopImage A true F I hI h3 k)) he)))

end SerrePositivity.KST.SConstruction
