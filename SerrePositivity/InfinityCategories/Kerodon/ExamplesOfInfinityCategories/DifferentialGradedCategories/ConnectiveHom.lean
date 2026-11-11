module

public import SerrePositivity.DifferentialGraded.Category.Basic
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.Algebra.Homology.Embedding.TruncLE
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.AlgebraicTopology.DoldKan.Equivalence
public import Mathlib.Tactic.CrossRefAttribute

/-!
# 切断した Hom 複体と Mathlib の Dold–Kan 対象

概要：Hom 複体の非正切断を次数反転して非負 chain 複体にし、Mathlib の Γ を適用する。
方針：ℕ から ℤ への n↦−n の埋め込みに沿う smart truncation を使う。
規約：零次数は Hom の零次数の項そのものではなく閉元となる。
使われ方：HA 1.3.1.13、Kerodon 2.5.6（Tag 00QQ）・2.5.9（Tag 00SC） の DK(τ^{≤0} Hom) の定義。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded

variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：Hom 複体の非正切断を次数反転した非負 chain 複体を取る。
方針：n↦0−n の shape 埋め込みに沿う Mathlib の smart truncation を用いる。
規約：微分の符号は変更しない。
使われ方：HA 1.3.1.13、Kerodon 2.5.6（Tag 00QQ） の Dold–Kan に渡す複体。 -/
def connectiveHomComplex (x y : D) : ChainComplex (ModuleCat.{u} R) ℕ :=
  (homObject R D x y).truncLE' (ComplexShape.embeddingUpIntLE 0)

/-- 概要：切断した Hom の零次数は元の Hom 複体の閉元の対象と同型である。
方針：切断の境界次数での cycles との同型を使う。
規約：ホモロジーへの商を取らない。
使われ方：HA 1.3.1.13 の閉零射と DK の零単体の比較。 -/
def connectiveHomComplex_zeroIso (x y : D) :
    (connectiveHomComplex (R := R) x y).X 0 ≅ (homObject R D x y).cycles 0 :=
  (homObject R D x y).truncLE'XIsoCycles (ComplexShape.embeddingUpIntLE 0)
    (by simp) ((ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 0).mpr rfl)

/-- 概要：切断した Hom の正次数 n+1 は元の Hom の次数 −(n+1) と同型である。
方針：切断の境界外の項の同型を使う。
規約：対象の宇宙と係数環の宇宙を独立に保つ。
使われ方：HA 1.3.1.13 の次数反転による Hom の成分計算。 -/
def connectiveHomComplex_positiveIso (x y : D) (n : ℕ) :
    (connectiveHomComplex (R := R) x y).X (n + 1) ≅
      (homObject R D x y).X (-(n + 1 : ℤ)) :=
  (homObject R D x y).truncLE'XIso (ComplexShape.embeddingUpIntLE 0) (by simp)
    (by rw [ComplexShape.boundaryLE_embeddingUpIntLE_iff]; omega)

/-- 概要：切断した Hom の零次数を具体的な閉次数零元の加群に同定する。
方針：抽象的 cycles と ModuleCat の核の同型を合成する。
規約：従来の zeroCycles と同じ線形核を用いる。
使われ方：HA 1.3.1.13、Kerodon 2.5.9.3（Tag 00SF） の閉零射との対応。 -/
def connectiveHomComplex_zeroCyclesIso (x y : D) :
    (connectiveHomComplex (R := R) x y).X 0 ≅
      ModuleCat.of R (zeroCycles (homObject R D x y)) :=
  connectiveHomComplex_zeroIso (R := R) x y ≪≫
    (homObject R D x y).cyclesIsoSc' (-1) 0 1 (by simp) (by simp) ≪≫
      ((homObject R D x y).sc' (-1) 0 1).moduleCatCyclesIso

/-- 概要：正次数間の切断した Hom の微分は元の Hom の微分である。
方針：切断の境界外の微分の計算式を使う。
規約：同型で移送した式を述べ、追加の符号は挿入しない。
使われ方：HA 1.3.1.12–1.3.1.13 の標準 chain map 方程式との比較。 -/
lemma connectiveHomComplex_d_positive (x y : D) (n : ℕ) :
    (connectiveHomComplex (R := R) x y).d (n + 2) (n + 1) =
      (connectiveHomComplex_positiveIso (R := R) x y (n + 1)).hom ≫
        (homObject R D x y).d (-(n + 2 : ℤ)) (-(n + 1 : ℤ)) ≫
          (connectiveHomComplex_positiveIso (R := R) x y n).inv := by
  exact (homObject R D x y).truncLE'_d_eq (ComplexShape.embeddingUpIntLE 0)
    (by simp) (by simp; omega) (by simp)
    (by rw [ComplexShape.boundaryLE_embeddingUpIntLE_iff]; omega)

/-- 概要：次数1から0への微分は元の微分を閉元へ因子分解した射である。
方針：切断の境界での微分の計算式を使う。
規約：零次数の項を丸ごと残す切断ではないことを明示する。
使われ方：HA 1.3.1.13 の DK の smart truncation の検査。 -/
lemma connectiveHomComplex_d_zero (x y : D) :
    (connectiveHomComplex (R := R) x y).d 1 0 =
      (connectiveHomComplex_positiveIso (R := R) x y 0).hom ≫
        (homObject R D x y).toCycles (-1) 0 ≫
          (connectiveHomComplex_zeroIso (R := R) x y).inv := by
  exact (homObject R D x y).truncLE'_d_eq_toCycles (ComplexShape.embeddingUpIntLE 0)
    (by simp) (by simp) (by simp)
    ((ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 0).mpr rfl)

/-- 概要：切断した Hom 複体の Mathlib の Dold–Kan 単体的加群を定義する。
方針：非負 chain 複体に Abelian.DoldKan.Γ をそのまま適用する。
規約：標準成分模型との同型はこの定義には仮定しない。
使われ方：HA 1.3.1.13 の DK(τ^{≤0} Hom) そのもの。 -/
def doldKanHomModule (x y : D) : SimplicialObject (ModuleCat.{u} R) :=
  (CategoryTheory.Abelian.DoldKan.Γ : ChainComplex (ModuleCat.{u} R) ℕ ⥤
    SimplicialObject (ModuleCat.{u} R)).obj (connectiveHomComplex (R := R) x y)

/-- 概要：Mathlib の Dold–Kan Hom の台単体集合を定義する。
方針：単体的加群の後に忘却関手を合成する。
規約：この時点では標準成分模型との同型や豊穣合成を主張しない。
使われ方：HA 1.3.1.13、Kerodon 2.5.9.2（Tag 00SE） の厳密な DK Hom。 -/
@[kerodon 00SE]
def doldKanHomSpace (x y : D) : SSet.{u} :=
  doldKanHomModule (R := R) x y ⋙ forget (ModuleCat.{u} R)

/-- 概要：Mathlib の DK Hom の正規化 Moore 複体は切断した Hom 複体と同型である。
方針：既存の Dold–Kan 同値の counit を実際の切断複体で評価する。
規約：標準成分模型側の正規化との比較を仮定していない。
使われ方：HA 1.3.1.13、Kerodon 2.5.6（Tag 00QQ） の Mathlib Γ との比較の標的側。 -/
def doldKanHomNormalizationIso (x y : D) :
    (AlgebraicTopology.normalizedMooreComplex (ModuleCat.{u} R)).obj
      (doldKanHomModule (R := R) x y) ≅ connectiveHomComplex (R := R) x y :=
  (CategoryTheory.Abelian.DoldKan.equivalence : SimplicialObject (ModuleCat.{u} R) ≌
    ChainComplex (ModuleCat.{u} R) ℕ).counitIso.app (connectiveHomComplex (R := R) x y)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
