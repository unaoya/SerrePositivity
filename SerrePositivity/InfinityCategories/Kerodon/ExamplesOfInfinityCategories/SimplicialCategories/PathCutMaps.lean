module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathCutReindex

/-!
概要：切替前の最大座標の射の合成・添字変換の計算則。
方針：標準単体の各頂点で path の最大元の公式を適用する。
規約：切替点を越える前後の二種類の合成を区別する。
使われ方：三対象の coherent な合成 prism の豊穣合成則。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：最大座標の標準単体への射は各頂点で最大元を返す。
方針：nerve と標準単体の同型の評価を計算する。
規約：path の旗の全ての頂点で成立する。
使われ方：Hom 上の射の等式を最大座標の等式へ戻す。 -/
lemma pathCutMaximumMap_apply {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i : Fin (n + 1)} (hi : t i = 0) (j : Fin (n + 2)) {d : ℕ}
    (P : (nerve (Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up j))) _⦋d⦌) (k : Fin (d + 1)) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximumMap t hi j).app (Opposite.op ⦋d⦌) P) k =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum t hi (P.obj k) := rfl

/-- 概要：切断点が零ラベルなら合成後の座標射は後半の座標射。
方針：各 path の旗で零ラベルの合成則を使う。
規約：k は追加した最後の頂点でもよい。
使われ方：豊穣恒等を左から合成する場合の非定値 Hom の計算。 -/
lemma pathCutMaximumMap_comp_zero {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hi : t i = 0) (hj : t j = 0) (k : Fin (n + 2)) :
    eComp SSet (⟨ULift.up i.castSucc⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
        ⟨ULift.up j.castSucc⟩ ⟨ULift.up k⟩ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximumMap t hi k =
      snd _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximumMap t hj k := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨P, Q⟩
  apply stdSimplex.ext
  intro l
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum_comp_zero t hi hj (P.obj l) (Q.obj l)

/-- 概要：切断点が一ラベルなら合成後の座標射は前半の座標射。
方針：各 path の旗で一ラベルの合成則を使う。
規約：後半の path は零ラベルの点を追加できない。
使われ方：二つの非定値の豊穣 Hom の合成の最初の座標。 -/
lemma pathCutMaximumMap_comp_one {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hi : t i = 0) (hj : t j = 1) (k : Fin (n + 2)) :
    eComp SSet (⟨ULift.up i.castSucc⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
        ⟨ULift.up j.castSucc⟩ ⟨ULift.up k⟩ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximumMap t hi k =
      fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximumMap t hi j.castSucc := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨P, Q⟩
  apply stdSimplex.ext
  intro l
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum_comp_one t hi hj (P.obj l) (Q.obj l)

/-- 概要：最後の頂点を固定する添字変換は任意の終点の path の関手。
方針：部分集合の像は包含を保つ。
規約：終点の添字にも同じ延長写像を使う。
使われ方：座標射の面・退化の自然性を nerve で表す。 -/
def pathCutReindexFunctor {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1))
    (j : Fin (m + 2)) :
    Path (ULift.up i.castSucc : ULift.{u} (Fin (m + 2))) (ULift.up j) ⥤
      Path (ULift.up (α.toOrderHom i).castSucc : ULift.{u} (Fin (n + 2)))
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom j)) where
  obj P := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutReindex α P
  map f := ⟨⟨⟨Set.image_mono f.1.1.1⟩⟩⟩

/-- 概要：切替前の座標射は面・退化を含む全ての単体圏の射と可換。
方針：各 path の旗の各頂点で最大座標の添字変換を適用する。
規約：始点の零ラベルは引き戻したラベルで判定する。
使われ方：パラメーター付き coherent な合成の単体的な自然性。 -/
lemma pathCutMaximumMap_reindex {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (t : Fin (n + 1) →o Fin 2) {i : Fin (m + 1)} (hi : t (α.toOrderHom i) = 0)
    (j : Fin (m + 2)) :
    nerveMap (pathCutReindexFunctor α i j) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximumMap t hi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom j) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximumMap (t.comp α.toOrderHom) hi j ≫ stdSimplex.map α := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro P
  apply stdSimplex.ext
  intro k
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum_reindex α t hi (P.obj k)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
