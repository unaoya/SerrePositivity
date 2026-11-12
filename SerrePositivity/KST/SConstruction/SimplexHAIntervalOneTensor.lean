module
public import SerrePositivity.KST.SConstruction.SimplexHAStrictIntervalSplit
public import SerrePositivity.KST.SConstruction.SimplexHAChainLiftTransport
public import SerrePositivity.KST.SConstruction.SerreCubeTensorCompositionTransport
public import SerrePositivity.KST.SConstruction.SimplexHAIntervalHomMap
public import SerrePositivity.KST.SConstruction.SimplexHAChainLiftFaces

/-! # 元の厳密二区間 HA 復元の実一面合成
概要：全区間 HA 鎖射の共有頂点一面への制限は、元の左右区間の実 tensor 合成。
方針：元の全区間列の切断を照合し、無条件の内部一面公式に次元移送を適用する。
規約：元の実鎖射・三頂点・因子順を保持。使われ方：native HA 逆 dg 関手の合成保存。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の全区間 HA 鎖射は、共有頂点の実一面で元の左右区間の実 tensor 合成を回収。 -/
lemma simplexHAIntervalChainLift_one_tensor {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (a b c : Fin (N + 1)) (hab : a < b) (hbc : b < c) :
    (serreCubeRightFace A true (b.val - a.val - 1) (c.val - b.val - 1)).hom ≫
      eqToHom (congrArg (serreCubeComplex A)
        (simplexHAStrictInterval_split_dimension a b c hab hbc).symm) ≫
          simplexHAIntervalChainLift A s a c (hab.trans hbc) =
      serreCubeTensorComposition A (b.val - a.val - 1) (c.val - b.val - 1)
        (simplexHAIntervalChainLift A s a b hab) (simplexHAIntervalChainLift A s b c hbc) := by
  let n := b.val - a.val - 1
  let m := c.val - b.val - 1
  let w := simplexHAStrictIntervalSplitOrder a b c hab hbc
  let cut := simplexHASplitCut n m w
  have hb := simplexHAStrictIntervalSplitOrder_last_lt a b c hab hbc
  have hx := simplexHAStrictIntervalSplitOrder_first a b c hab hbc
  have hy := simplexHAStrictIntervalSplitOrder_cut a b c hab hbc
  have hleft := simplexHAChainLift_heq A s (rfl : n = n)
    (simplexHASplitLeft n m w) (simplexHAStrictIntervalOrder a b hab)
    (heq_of_eq (simplexHAStrictIntervalSplitOrder_left a b c hab hbc)) cut b hy
    (simplexHASplitLeft_last_lt n m w) (simplexHAStrictIntervalOrder_last_lt a b hab)
  have hright := simplexHAChainLift_heq A s (rfl : m = m)
    (simplexHASplitRight n m w) (simplexHAStrictIntervalOrder b c hbc)
    (heq_of_eq (simplexHAStrictIntervalSplitOrder_right a b c hab hbc)) c c rfl
    (lt_of_eq_of_lt (simplexHASplitRight_last n m w) hb)
    (simplexHAStrictIntervalOrder_last_lt b c hbc)
  have hcomp := serreCubeTensorComposition_heq A (rfl : n = n) (rfl : m = m)
    (congrArg s.obj hx) (congrArg s.obj hy) (rfl : s.obj c = s.obj c)
    (simplexHAChainLift A s n (simplexHASplitLeft n m w) cut
      (simplexHASplitLeft_last_lt n m w))
    (simplexHAChainLift A s m (simplexHASplitRight n m w) c
      (lt_of_eq_of_lt (simplexHASplitRight_last n m w) hb))
    (simplexHAIntervalChainLift A s a b hab) (simplexHAIntervalChainLift A s b c hbc)
    hleft hright
  have hone := simplexHAChainLift_one_tensor A s n m w c hb
  have hdim := simplexHAChainLift_dimension A s
    (simplexHAStrictInterval_split_dimension a b c hab hbc)
    (simplexHAStrictIntervalOrder a c (hab.trans hbc)) c
    (simplexHAStrictIntervalOrder_last_lt a c (hab.trans hbc)) hb
  let e := eqToHom (congrArg (fun x => homObject A D (s.obj x) (s.obj c)) hx)
  have hnorm : (serreCubeRightFace A true n m).hom ≫
      eqToHom (congrArg (serreCubeComplex A)
        (simplexHAStrictInterval_split_dimension a b c hab hbc).symm) ≫
          simplexHAIntervalChainLift A s a c (hab.trans hbc) =
        ((serreCubeRightFace A true n m).hom ≫ simplexHAChainLift A s (n + 1 + m) w c hb) ≫
          e :=
    (congrArg (fun f => (serreCubeRightFace A true n m).hom ≫ f) hdim.symm).trans
      (Category.assoc _ _ _).symm
  exact hnorm.trans ((congrArg (fun f => f ≫ e) hone).trans
    (eq_of_heq ((comp_eqToHom_heq _ _).trans hcomp)))

end SerrePositivity.KST.SConstruction
