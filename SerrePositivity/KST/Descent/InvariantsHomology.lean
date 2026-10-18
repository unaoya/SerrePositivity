module

public import SerrePositivity.KST.Descent.InvariantExactness
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# 有理不変部分とホモロジーの可換性

## 概要
有限群の有理不変部分関手が全射とホモロジーを保つことを証明する。

## 方針
平均による不変な持ち上げから epi 保存を得る。
不変部分関手は右随伴なので kernel を保ち、epi 保存と合わせてホモロジーを保つ。

## 規約
任意の短複体のホモロジーで主張し、複体の有界性は仮定しない。
スペクトルの hG との同定や非有界な二重複体の Tot はここでは扱わない。

## 使われ方
論文 (3.8) の有理固定点の π_* 側、軌道正方形に対する長完全列の完全性。
-/

@[expose] public section

open CategoryTheory Representation Rep

namespace SerrePositivity.KST.Descent

universe u v

variable (G : Type u) [Group G] [Finite G]

/-- 概要：有限群の有理不変部分関手は全射を保つ（論文 定理 3.1、(3.8)）。
方針：表現の epi を加群の全射と読み替え、平均による不変な持ち上げを使う。
規約：表現の加群の有限次元性は要求しない。
使われ方：kernel 保存と合わせたホモロジー保存。 -/
instance rationalInvariants_preservesEpimorphisms :
    (invariantsFunctor ℚ G : Rep.{v} ℚ G ⥤ ModuleCat.{v} ℚ).PreservesEpimorphisms where
  preserves f hf := by
    apply (ModuleCat.epi_iff_surjective _).mpr
    exact invariantMap_surjective f.hom ((Rep.epi_iff_surjective f).mp hf)

/-- 概要：有限群の有理不変部分関手はホモロジーを保つ（論文 定理 3.1、(3.8)）。
方針：右随伴による kernel 保存と、平均による epi 保存を組み合わせる。
規約：各次数で使えるので、有界な複体への制限や収束の仮定は不要。
使われ方：全次数の長完全列や (3.8) の π_* 計算に接続する。 -/
instance rationalInvariants_preservesHomology :
    (invariantsFunctor ℚ G : Rep.{v} ℚ G ⥤ ModuleCat.{v} ℚ).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels (invariantsFunctor ℚ G)

/-- 概要：不変部分を取ってから計算したホモロジーとホモロジーの不変部分の同型（(3.8)）。
方針：証明済みのホモロジー保存から標準の比較同型を取る。
規約：任意の短複体への主張であり、任意の整数次数の隣接三項に適用できる。
使われ方：非有界な場合にも次数ごとの計算を正当化する代数的な部品。 -/
noncomputable def invariantsHomologyIso (S : ShortComplex (Rep.{v} ℚ G)) :
    (S.map (invariantsFunctor ℚ G)).homology ≅
      (invariantsFunctor ℚ G).obj S.homology :=
  S.mapHomologyIso (invariantsFunctor ℚ G)

end SerrePositivity.KST.Descent
