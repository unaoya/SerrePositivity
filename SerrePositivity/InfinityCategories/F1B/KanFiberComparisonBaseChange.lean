module

public import SerrePositivity.InfinityCategories.F1B.VertexFiberBaseChange
public import SerrePositivity.InfinityCategories.Core.VertexFiberMap
public import SerrePositivity.InfinityCategories.F1.Diagrams.OverPullbackMorphism

/-!
概要：底を保つ比較射の引き戻しと、その fiber の自然性。
方針：比較射を第一成分に作用させ、各 fiber の標準同型で元の比較と照合する。
規約：引き戻しは元の射影を左、底変換の射を右に置く。
使われ方：Kerodon Corollary 5.6.0.6、fiber ごとの同値判定の底変換。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：底を保つ比較射を任意の底の射に沿って引き戻す。
方針：第一射影に比較射を合成し、第二射影を保って pullback へ持ち上げる。
規約：充填性や同値性を仮定しない。
使われ方：Kerodon Remark 5.6.2.5、局所的な fiber 比較の全空間の射。 -/
noncomputable def kanFiberComparisonBaseChange {E E' B K : SSet.{u}}
    (p : E ⟶ B) (q : E' ⟶ B) (f : E ⟶ E') (hf : f ≫ q = p) (g : K ⟶ B) :
    pullback p g ⟶ pullback q g :=
  pullback.lift (pullback.fst p g ≫ f) (pullback.snd p g) (by
    rw [Category.assoc, hf, pullback.condition])

/-- 概要：引き戻した比較射は新しい底を保つ。
方針：pullback の持ち上げの第二射影の式を使う。
規約：第二射影は同じ底 K への射。
使われ方：Kerodon Remark 5.6.2.5、引き戻した比較の fiber 射。 -/
lemma kanFiberComparisonBaseChange_projection {E E' B K : SSet.{u}}
    (p : E ⟶ B) (q : E' ⟶ B) (f : E ⟶ E') (hf : f ≫ q = p) (g : K ⟶ B) :
    kanFiberComparisonBaseChange p q f hf g ≫ pullback.snd q g = pullback.snd p g :=
  pullback.lift_snd _ _ _

/-- 概要：引き戻した比較の fiber 射は、標準 fiber 同型で元の像の頂点の比較射に一致する。
方針：元の全空間へ含め、二つの pullback の第一射影を計算する。
規約：fiber の頂点は g の零次成分で写す。
使われ方：Kerodon Corollary 5.6.0.6、fiber ごとの同値を各標準単体へ引き戻す。 -/
lemma kanFiberComparisonBaseChange_fiber {E E' B K : SSet.{u}}
    (p : E ⟶ B) (q : E' ⟶ B) (f : E ⟶ E') (hf : f ≫ q = p)
    (g : K ⟶ B) (k : K _⦋0⦌) :
    vertexFiberMap (pullback.snd p g) (pullback.snd q g)
        (kanFiberComparisonBaseChange p q f hf g)
        (kanFiberComparisonBaseChange_projection p q f hf g) k ≫
      (cofinalVertexFiberBaseChangeIso q g k).hom =
    (cofinalVertexFiberBaseChangeIso p g k).hom ≫
      vertexFiberMap p q f hf (g.app (Opposite.op ⦋0⦌) k) := by
  apply vertexFiber_hom_ext
  simp only [Category.assoc, cofinalVertexFiberBaseChangeIso_hom_ι, vertexFiberMap_ι]
  simp only [← Category.assoc, vertexFiberMap_ι, cofinalVertexFiberBaseChangeIso_hom_ι]
  simp only [Category.assoc, kanFiberComparisonBaseChange, pullback.lift_fst]

/-- 概要：比較射の底変換は Over 圏の pullback 比較と pullback の交換同型で一致する。
方針：両射影へ合成し、第一成分の比較と第二成分の恒等を確認する。
規約：Over 圏の pullback は底の対象を第一成分に置く。
使われ方：Kerodon Corollary 5.6.0.6、底の単体による局所性への適用。 -/
lemma kanFiberComparisonBaseChange_overPullbackMap {E E' B K : SSet.{u}}
    (p : E ⟶ B) (q : E' ⟶ B) (f : E ⟶ E') (hf : f ≫ q = p) (g : K ⟶ B) :
    (pullbackSymmetry g p).hom ≫ kanFiberComparisonBaseChange p q f hf g =
      overPullbackMap (Over.homMk (U := Over.mk p) (V := Over.mk q) f hf) (Over.mk g) ≫
        (pullbackSymmetry g q).hom := by
  apply pullback.hom_ext
  · simp only [Category.assoc, kanFiberComparisonBaseChange, pullback.lift_fst,
      pullbackSymmetry_hom_comp_fst, overPullbackMap, Over.mk_hom,
      pullback.lift_snd, Over.homMk_left]
    rw [← Category.assoc, pullbackSymmetry_hom_comp_fst]
  · simp only [Category.assoc, kanFiberComparisonBaseChange, pullback.lift_snd,
      pullbackSymmetry_hom_comp_snd, overPullbackMap, Over.mk_hom, pullback.lift_fst]

end SerrePositivity.InfinityCategories.F1B
