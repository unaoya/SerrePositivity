module

public import SerrePositivity.InfinityCategories.F1.Diagrams.SimplicialReplacementBaseChange
public import SerrePositivity.InfinityCategories.Core.VertexFiberNervePullback

/-!
概要：simplicial replacement の底を保つ射の fiber と底変換。
方針：left・cocartesian 両 scaffold の汎用の射を同じ原本から使う。
規約：元の宣言名・型・証明本文を保持する。
使われ方：F1 と F1B の共通の幾何的な計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：底を保つ simplicial replacement の射が各係数値から誘導する fiber 比較。
方針：定値の底への標準包含に比較射を合成して、射影の可換性により fiber へ持ち上げる。
規約：底上の可換性 h は厳密な射の等式。
使われ方：Kerodon Definition 5.3.4.2、scaffold の係数値ごとの条件。 -/
def leftScaffoldFiberMap {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) (F : C ⥤ SSet.{u}) (l : simplicialReplacement F ⟶ E)
    (h : l ≫ p = simplicialReplacementProjection F) (c : C) :
    F.obj c ⟶ vertexFiber p (nerveVertex c) :=
  vertexFiberLift _ _ (simplicialReplacementConstantLift F c ≫ l) (by
    rw [Category.assoc, h, simplicialReplacementConstantLift_projection])

/-- 概要：底を保つ simplicial replacement の比較射を新しい底へ引き戻す。
方針：元の比較射と新しい底の射影を引き戻しの普遍性で組にする。
規約：h は元の比較射の底上の可換性。
使われ方：Kerodon Remark 5.3.2.3、scaffold の底変換の比較射。 -/
noncomputable def leftScaffoldBaseChange
    {C D : Type u} [Category.{u} C] [Category.{u} D] {E : SSet.{u}}
    (p : E ⟶ nerve C) (F : C ⥤ SSet.{u}) (l : simplicialReplacement F ⟶ E)
    (h : l ≫ p = simplicialReplacementProjection F) (H : D ⥤ C) :
    simplicialReplacement (H ⋙ F) ⟶ pullback p (nerveMap H) :=
  pullback.lift (simplicialReplacementBaseMap H F ≫ l) (simplicialReplacementProjection (H ⋙ F))
    (by rw [Category.assoc, h, simplicialReplacementBaseMap_projection])

end SerrePositivity.InfinityCategories
