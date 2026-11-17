# Ind-S：二短辺と全 native 長 Hom による二単体の厳密外延性

概要：採用済み (9)・(9b) の各入力点で、元の実二単体そのものを回収するための補題。
方針：元の二短辺の厳密一致と全 native 長 Hom の HEq を使う。
規約：F1 正本の補題として依頼する。K-B に汎用証明を複製しない。quasicategory 性は不要。
使われ方：正規化前後・制御前後の各 K 頂点の二単体を、同じ元の二単体へ厳密に戻す。

- 既存の triangleReplaceLongHom_self は自己置換を回収するが、別々の二単体の外延性の公開名は未確認。
- 同じ型の既存公開定理があれば、その名前の指定でよい。証明や新たな存在入力はここで追加しない。
- 下記は供給命題の型のみ。作業コピー `/tmp/kb-native-triangle-ext-request.lean`。

```lean
import SerrePositivity.InfinityCategories.F1.Diagrams.TriangleLongHomReplacement
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
universe u v

def kbNativeTriangleExtRequest : Prop :=
  ∀ (C : Type v) [Category.{u} C] [SimplicialCategory C]
    (F G : (SimplicialNerve C) _⦋2⦌),
    (SimplicialNerve C).δ (0 : Fin 3) F = (SimplicialNerve C).δ (0 : Fin 3) G →
    (SimplicialNerve C).δ (2 : Fin 3) F = (SimplicialNerve C).δ (2 : Fin 3) G →
    HEq (F.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)
      (G.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩) → F = G
```
