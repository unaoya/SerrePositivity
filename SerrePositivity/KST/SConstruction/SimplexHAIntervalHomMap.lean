module
public import SerrePositivity.KST.SConstruction.SimplexHAStrictIntervalOrder
public import SerrePositivity.KST.SConstruction.SimplexHAChainLiftRecovery
public import SerrePositivity.KST.SConstruction.SimplexIntervalLambdaHom

/-! # 元の厳密区間の Λ Hom からの native HA 逆鎖射
概要：元の a<b の全内部頂点の実 HA 鎖射を、元の Λ Hom の実同型で戻す。
方針：同じ厳密区間の頂点列と、元の全 necklace の Hom 比較を合成する。
規約：元の全高次 Hom と端点を保持。使われ方：native HA 単体からの逆 dg 関手。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の厳密区間の全内部頂点を使う、元の HA 実 Hom 鎖射。 -/
def simplexHAIntervalChainLift {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (a b : Fin (N + 1)) (hab : a < b) :
    serreCubeComplex A (b.val - a.val - 1) ⟶ homObject A D (s.obj a) (s.obj b) :=
  simplexHAChainLift A s (b.val - a.val - 1) (simplexHAStrictIntervalOrder a b hab) b
    (simplexHAStrictIntervalOrder_last_lt a b hab)

/-- 元の厳密区間の Λ Hom から、元の HA 値を保つ実 Hom 鎖射を得る。 -/
def simplexHAIntervalHomMap {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (a b : Fin (N + 1)) (hab : a < b) :
    homObject A (CubicalLambda A (Δ[N] : SSet.{u}))
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) ⟶ homObject A D (s.obj a) (s.obj b) :=
  (simplexIntervalLambdaHomIso A a b hab.le).inv ≫ simplexHAIntervalChainLift A s a b hab

/-- 元の厳密区間の Hom 同型への制限は、元の同じ HA 実鎖射を厳密に回収する。 -/
lemma simplexHAIntervalHomMap_restrict {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (a b : Fin (N + 1)) (hab : a < b) :
    (simplexIntervalLambdaHomIso A a b hab.le).hom ≫ simplexHAIntervalHomMap A s a b hab =
      simplexHAIntervalChainLift A s a b hab := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ simplexHAIntervalChainLift A s a b hab)
      (simplexIntervalLambdaHomIso A a b hab.le).hom_inv_id).trans (Category.id_comp _))

/-- 元の厳密区間の逆 Hom 鎖射は、元の厳密 dg 後合成と可換。 -/
lemma simplexHAIntervalHomMap_post {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    {E : Type w} [DGCategory A E] (F : DGFunctor A D E)
    (a b : Fin (N + 1)) (hab : a < b) :
    simplexHAIntervalHomMap A (s.map F) a b hab =
      simplexHAIntervalHomMap A s a b hab ≫ F.map (s.obj a) (s.obj b) := by
  have h := congrArg (fun f => (simplexIntervalLambdaHomIso A a b hab.le).inv ≫ f)
    (simplexHAChainLift_post A s F (b.val - a.val - 1) (simplexHAStrictIntervalOrder a b hab) b
      (simplexHAStrictIntervalOrder_last_lt a b hab))
  exact h.trans (Category.assoc _ _ _).symm

end SerrePositivity.KST.SConstruction
