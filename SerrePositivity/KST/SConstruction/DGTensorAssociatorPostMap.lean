module
public import SerrePositivity.KST.SConstruction.DGTensorAssociator

/-! # 実 dg 結合関手の後合成の Hom 公式
概要：実 tensor の結合関手の後に任意の dg 関手を合成したときの全 Hom を固定する。
方針：一般の dg 圏のまま合成と対象の組を評価し、巨大な出力模型の展開を避ける。
規約：元の結合射と対象作用を保持。使われ方：ラベル付き Perf 右作用の合成比較。
-/
@[expose] public section
noncomputable section
universe u v w z t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (C : Type v) (D : Type w) (E : Type z) {B : Type t}
  [DGCategory A C] [DGCategory A D] [DGCategory A E] [DGCategory A B]

/-- 実結合関手の後合成の Hom は、元の結合射に続く同じ dg Hom 作用。 -/
lemma dgTensorAssociator_post_map
    (F : DGFunctor A (DGTensorCategory A C (DGTensorCategory A D E)) B)
    (x y : DGTensorCategory A (DGTensorCategory A C D) E) :
    (DGFunctor.comp (dgTensorAssociator A C D E) F).map x y =
      (α_ (homObject A C x.1.1 y.1.1) (homObject A D x.1.2 y.1.2)
        (homObject A E x.2 y.2)).hom ≫ F.map (x.1.1, (x.1.2, x.2)) (y.1.1, (y.1.2, y.2)) := rfl

end SerrePositivity.KST.SConstruction
