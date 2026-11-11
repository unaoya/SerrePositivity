module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# 単体作用素の列の終端頂点パラメータ

概要：反対要素圏の nerve から元の単体集合へ送る実際の頂点パラメータを作る。
方針：列の各単体の最後の頂点を同じ終端単体へ送り、尾の合成則で自然性を示す。
規約：最終頂点を変える面や退化も全て含む。
使われ方：Dwyer–Kan §7 の共通比較の frame 側の実際の augmentation。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SimplexTerminalParameter

open CategoryTheory

variable {n : ℕ} (c : Fin (n + 1) ⥤ SimplexCategory)

/-- 概要：元の列の終端への尾は二つの尾の合成（Dwyer–Kan §7）。
方針：元の射列の関手の合成則を使う。
規約：頂点の大小に関する同じ射を使う。
使われ方：終端パラメータの単調性と全 reindexing。 -/
lemma tail_comp {i j : Fin (n + 1)} (h : i ≤ j) :
    c.map (homOfLE (Fin.le_last i)) =
      c.map (homOfLE h) ≫ c.map (homOfLE (Fin.le_last j)) := c.map_comp _ _

/-- 概要：各頂点の最後の頂点を同じ終端単体へ送る（Dwyer–Kan §7）。
方針：元の尾の単体作用素を評価する。
規約：終端単体の同じ頂点の型。
使われ方：単調な終端パラメータの値。 -/
abbrev vertex (i : Fin (n + 1)) : Fin ((c.obj (Fin.last n)).len + 1) :=
  (c.map (homOfLE (Fin.le_last i))).toOrderHom (Fin.last (c.obj i).len)

/-- 概要：元の終端頂点の表示は単調（Dwyer–Kan §7）。
方針：尾の合成則と各単体の最後の頂点の最大性を使う。
規約：異なる次元の単体を同じ終端単体内で比較する。
使われ方：実際の単体圏の射の構成。 -/
lemma monotone : Monotone (vertex c) := by
  intro i j h
  have e := congrArg (fun f => f.toOrderHom (Fin.last (c.obj i).len)) (tail_comp c h)
  change vertex c i = (c.map (homOfLE (Fin.le_last j))).toOrderHom
    ((c.map (homOfLE h)).toOrderHom (Fin.last (c.obj i).len)) at e
  rw [e]
  exact (c.map (homOfLE (Fin.le_last j))).toOrderHom.monotone (Fin.le_last _)

/-- 概要：射列の実際の終端頂点パラメータ（Dwyer–Kan §7）。
方針：同じ頂点写像と単調性を単体作用素へ束ねる。
規約：元の列と終端対象を保持する。
使われ方：反対要素圏の nerve の augmentation。 -/
def parameter : SimplexCategory.mk n ⟶ c.obj (Fin.last n) :=
  SimplexCategory.Hom.mk ⟨vertex c, monotone c⟩

/-- 概要：終端パラメータは全頂点で元の尾の値（Dwyer–Kan §7）。
方針：定義を評価する。
規約：同じ頂点の型。
使われ方：augmentation の全作用素の照合。 -/
lemma parameter_apply (i : Fin (n + 1)) : (parameter c).toOrderHom i = vertex c i := rfl

/-- 概要：終端パラメータは最後の頂点を最後の頂点へ送る（Dwyer–Kan §7）。
方針：同じ列の終端での恒等射を評価する。
規約：元の終端単体の最後の頂点。
使われ方：終端における正規化。 -/
lemma parameter_last : (parameter c).toOrderHom (Fin.last n) = Fin.last _ := by
  change (c.map (𝟙 (Fin.last n))).toOrderHom (Fin.last _) = _
  rw [c.map_id]
  rfl

/-- 概要：終端パラメータは全 reindexing と尾の作用素で両立（Dwyer–Kan §7）。
方針：新しい終端から元の終端までの尾を保持して各頂点で合成則を使う。
規約：最終頂点を消す面も含み、終端保存は仮定しない。
使われ方：反対要素圏の nerve の全単体自然性。 -/
lemma reindex {m : ℕ} (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    θ ≫ parameter c =
      parameter ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) ≫
        c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m)))) := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  exact congrArg (fun f => f.toOrderHom (Fin.last (c.obj (θ.toOrderHom i)).len))
    (tail_comp c (θ.toOrderHom.monotone (Fin.le_last i)))

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SimplexTerminalParameter
