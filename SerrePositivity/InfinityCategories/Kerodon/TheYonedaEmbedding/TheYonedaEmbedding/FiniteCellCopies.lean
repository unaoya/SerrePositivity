module

public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
概要：有限形状からの全ての射で添字付けたセルの余積は filtered 余極限を保つ。
方針：有限表示性による Hom の保存と、余積の copower 随伴を合成する。
規約：セルの形状は任意だが、その添字に使う形状は有限とする。
使われ方：filtered 余極限を保つ明示的な Kan セル付加関手の構成。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 概要：A から X への全ての射につき B のコピーを一つずつ付ける関手。
方針：Hom(A,−) に B の copower 関手を合成する。
規約：対象の値は射の型で添字付けた実際の余積。
使われ方：ホーンごとに付加するセルの始域と終域。 -/
def cellCopiesFunctor (A B : SSet.{u}) : SSet.{u} ⥤ SSet.{u} :=
  coyoneda.obj (Opposite.op A) ⋙ sigmaConst.obj B

/-- 概要：有限な A に対するセルのコピー関手は小さい filtered 余極限を保つ。
方針：Hom(A,−) の有限表示性と copower の左随伴性を使う。
規約：単体集合と同じ宇宙の添字圏を扱う。
使われ方：明示的な Kan 置換の連続性の最初の部品。 -/
instance cellCopiesFunctor_preservesFilteredColimits (A B : SSet.{u}) [A.Finite] :
    PreservesFilteredColimitsOfSize.{u, u} (cellCopiesFunctor A B) := by
  have := (sigmaConstAdj B).leftAdjoint_preservesColimits
  dsimp only [cellCopiesFunctor]
  infer_instance

/-- 概要：A のコピーをその添字の射に沿って元の対象へ評価する。
方針：copower と Hom の随伴の余単位を使う。
規約：各コピーの制限は添字そのもの。使われ方：セル付加の pushout の上辺。 -/
def cellCopiesEvaluation (A : SSet.{u}) : cellCopiesFunctor A A ⟶ 𝟭 SSet.{u} :=
  (sigmaConstAdj A).counit

/-- 概要：セルの形状の射はコピー関手の自然変換を誘導する。
方針：同じ添字を保ち、copower の各コピーで元の射を使う。
規約：射を添字付ける始域 A は固定する。使われ方：セル付加の pushout の左辺。 -/
def cellCopiesMap (A : SSet.{u}) {B D : SSet.{u}} (i : B ⟶ D) :
    cellCopiesFunctor A B ⟶ cellCopiesFunctor A D :=
  Functor.whiskerLeft (coyoneda.obj (Opposite.op A)) (sigmaConst.map i)

/-- 概要：評価の各コピーへの制限は添字の元の射。
方針：余積からの射の制限を計算する。
規約：添字 t を固定する。使われ方：セル付加の可換条件。 -/
lemma cellCopiesEvaluation_ι {A X : SSet.{u}} (t : A ⟶ X) :
    Sigma.ι (fun _ : A ⟶ X ↦ A) t ≫ (cellCopiesEvaluation A).app X = t := by
  exact Sigma.ι_comp_desc _ _

/-- 概要：セルの射の自然変換は各コピー上で元の射に一致する。
方針：余積の射の制限の公式を使う。
規約：添字 t は変更しない。使われ方：付加したセルの境界の照合。 -/
lemma cellCopiesMap_ι {A B D X : SSet.{u}} (i : B ⟶ D) (t : A ⟶ X) :
    Sigma.ι (fun _ : A ⟶ X ↦ B) t ≫ (cellCopiesMap A i).app X =
      i ≫ Sigma.ι (fun _ : A ⟶ X ↦ D) t := by
  exact Sigma.ι_map (fun _ : A ⟶ X ↦ i) t

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
