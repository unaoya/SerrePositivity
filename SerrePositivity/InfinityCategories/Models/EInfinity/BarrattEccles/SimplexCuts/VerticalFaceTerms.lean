module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.VerticalFaceCoordinates
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.VerticalInputTerms

/-!
模型。文献の定義との比較は後で
# 全垂直同値の指定入力面で読む元の境界項

Berger–Fresse §2.2.7、M14 L09a。
既存の全垂直同値が選ぶ元の入力面と小さい切断に、実境界項の比較を貼り合わせる。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- C251：全垂直同値の指定面の元の境界項は、同じ入力面の切断項。 -/
lemma outputBoundaryTerm_verticalBoundaryFaceEquiv {m q r : ℕ} (S : SSet.{0})
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (c : Fin (q + 2) × _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticalBoundaryFaceEquiv m q c).val.1 v
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticalBoundaryFaceEquiv m q c).val.1 v.val
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticalBoundaryFaceEquiv m q c).val.2) + 1))
    (hj : j.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertexRank (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticalBoundaryFaceEquiv m q c).val.1 v.val
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticalBoundaryFaceEquiv m q c).val.1 v.val
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticalBoundaryFaceEquiv m q c).val.2) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticalBoundaryFaceEquiv m q c).val.2)
    (x : S _⦋q + 1⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundaryTerm A S (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticalBoundaryFaceEquiv m q c).val.1 v
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticalBoundaryFaceEquiv m q c).val.1 v.val
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticalBoundaryFaceEquiv m q c).val.2) j x =
      (-1 : ℤ) ^ (m + 1 - r + c.1.val) •
        (eqToHom (congrArg (fun z : ℤ => (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) r).X z)
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticalDeletion_degree_eq (q := q) v))).hom
            (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTerm A S c.2 v (S.δ c.1 x)) := by
  have ht := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundaryTerm_vertical_of_coordinates A S
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticalBoundaryFaceEquiv m q c).val.1 c.2 v
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticalBoundaryFaceEquiv m q c).val.2 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticalBoundaryFaceEquiv m q c).property
    (fun l => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticalBoundaryFaceEquiv_deleted_coordinates m q c l).1)
    (by intro l; rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticalBoundaryFaceEquiv_vertical];
        exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticalBoundaryFaceEquiv_deleted_coordinates m q c l).2) j hj x
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticalBoundaryFaceEquiv_vertical] using ht

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
