module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathCutMaximum

/-!
概要：path の切替前の最大座標の面・退化に関する自然性。
方針：最後の頂点固定延長で path の像を取り、最大元の像を比較する。
規約：終点は切替後の任意の頂点でも追加した最後の頂点でもよい。
使われ方：パラメーター付き豊穣合成 prism の単体的な自然性。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：最後の頂点を固定する添字変換で任意の終点の path を写す。
方針：path の部分集合の像を取り、端点の等式を入れる。
規約：始点は元の単体内に置く。
使われ方：切替前の座標の自然性の定義域。 -/
def pathCutReindex {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) {i : Fin (m + 1)} {j : Fin (m + 2)}
    (P : Path (ULift.up i.castSucc : ULift.{u} (Fin (m + 2))) (ULift.up j)) :
    Path (ULift.up (α.toOrderHom i).castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom j)) where
  I := (fun k : ULift.{u} (Fin (m + 2)) ↦
    ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom k.down)) '' P.I
  left := ⟨ULift.up i.castSucc, P.left, by
    exact ULift.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc _ _)⟩
  right := ⟨ULift.up j, P.right, rfl⟩
  left_le k hk := by
    obtain ⟨l, hl, rfl⟩ := hk
    change (α.toOrderHom i).castSucc ≤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom l.down
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom).monotone (P.left_le l hl)
  le_right k hk := by
    obtain ⟨l, hl, rfl⟩ := hk
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom).monotone (P.le_right l hl)

/-- 概要：切替前の最大座標は面・退化を含む全ての添字変換と可換。
方針：像の最大元の原像と、元の最大元の像を用いて両方向の不等式を示す。
規約：ラベルも同じ添字写像で引き戻す。
使われ方：coherent な合成 prism の全次数の自然性。 -/
lemma pathCutMaximum_reindex {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (t : Fin (n + 1) →o Fin 2) {i : Fin (m + 1)} (hi : t (α.toOrderHom i) = 0)
    {j : Fin (m + 2)}
    (P : Path (ULift.up i.castSucc : ULift.{u} (Fin (m + 2))) (ULift.up j)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum t hi (pathCutReindex α P) =
      α.toOrderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum (t.comp α.toOrderHom) hi P) := by
  apply le_antisymm
  · have hm := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum_spec t hi (pathCutReindex α P)).2
    obtain ⟨⟨k⟩, hk, he⟩ := hm
    induction k using Fin.lastCases with
    | last =>
      have he' := congrArg (fun k : ULift.{u} (Fin (n + 2)) ↦ k.down.val) he
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom (Fin.last (m + 1))).val =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum t hi (pathCutReindex α P)).val at he'
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last] at he'
      have hlt := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum t hi (pathCutReindex α P)).isLt
      change n + 1 = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum t hi (pathCutReindex α P)).val at he'
      omega
    | cast k =>
      have he' := congrArg (fun k : ULift.{u} (Fin (n + 2)) ↦ k.down.val) he
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom k.castSucc).val =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum t hi (pathCutReindex α P)).val at he'
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc] at he'
      have hmax : α.toOrderHom k = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum t hi (pathCutReindex α P) := Fin.ext he'
      have ht : (t.comp α.toOrderHom) k = 0 := by
        change t (α.toOrderHom k) = 0
        rw [hmax]
        exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum_spec t hi (pathCutReindex α P)).1
      rw [← hmax]
      exact α.toOrderHom.monotone (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.le_pathCutMaximum (t.comp α.toOrderHom) hi P k ht hk)
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.le_pathCutMaximum t hi (pathCutReindex α P)
    · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum_spec (t.comp α.toOrderHom) hi P).1
    · refine ⟨ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum (t.comp α.toOrderHom) hi P).castSucc,
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum_spec (t.comp α.toOrderHom) hi P).2, ?_⟩
      exact ULift.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc _ _)

/-- 概要：切替前の最大座標を取る操作は path の包含の関手。
方針：最大座標の単調性を順序射にする。
規約：標的を同じ宇宙の有限順序へ持ち上げる。
使われ方：豊穣 Hom 上の座標射の構成。 -/
noncomputable def pathCutMaximumFunctor {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i : Fin (n + 1)} (hi : t i = 0) (j : Fin (n + 2)) :
    Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) (ULift.up j) ⥤
      ULift.{u} (Fin (n + 1)) where
  obj P := ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum t hi P)
  map f := homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum_mono t hi f.1.1.1)

/-- 概要：切替前の最大座標を標準単体への射にする。
方針：座標を取る関手の nerve と標準単体の nerve 同型を合成する。
規約：二値ラベルの零側から始まる Hom に定義する。
使われ方：パラメーター付きの最初の豊穣 Hom の評価。 -/
noncomputable def pathCutMaximumMap {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i : Fin (n + 1)} (hi : t i = 0) (j : Fin (n + 2)) :
    nerve (Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) (ULift.up j)) ⟶
      (Δ[n] : SSet.{u}) :=
  nerveMap (pathCutMaximumFunctor t hi j) ≫ (stdSimplex.isoNerve n).inv

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
