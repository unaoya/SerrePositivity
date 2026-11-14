module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ChainTensorVanishing
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Alexander–Whitney の切断と成分写像

概要：単体の共有切断点による前半と後半を使い、通常の Alexander–Whitney の成分を構成する。
方針：n 単体の切断点 i に対し、次数 i と n−i の制限写像をテンソルして全複体へ入れる。
規約：KST Construction A.5 の比較。前半が第一因子、後半が第二因子。
使われ方：正規化したテンソルの消滅を単体的な次数ごとのテンソルへ戻す比較。
このファイルの成分構成だけでは鎖写像性・shuffle 比較の完成を主張しない。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory Opposite HomologicalComplex AlgebraicTopology
open scoped Simplicial

/-- 概要：n 単体の切断点までの前半の順序写像。
方針：頂点番号を保つ包含を使う。
規約：KST A.5 の AW、切断点を両因子で共有する。
使われ方：第一因子の制限写像。 -/
@[kerodon 00S1]
def awFront (n : ℕ) (i : Fin (n + 1)) : ⦋(i : ℕ)⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom
    { toFun j := ⟨j, by have := j.isLt; have := i.isLt; omega⟩
      monotone' _ _ h := h }

/-- 概要：n 単体の切断点からの後半の順序写像。
方針：頂点番号に切断点の番号を加える。
規約：KST A.5 の AW、後半の次数は n−i。
使われ方：第二因子の制限写像。 -/
@[kerodon 00S1]
def awBack (n : ℕ) (i : Fin (n + 1)) : ⦋n - (i : ℕ)⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom
    { toFun j := ⟨(i : ℕ) + j, by have := j.isLt; have := i.isLt; omega⟩
      monotone' _ _ h := Nat.add_le_add_left h _ }

/-- 概要：前半への包含は頂点の番号を保つ。
方針：順序写像の定義を評価する。
規約：KST A.5 の AW。使われ方：面写像との切断公式。 -/
@[simp] lemma awFront_apply (n : ℕ) (i : Fin (n + 1)) (j : Fin ((i : ℕ) + 1)) :
    ((awFront n i).toOrderHom j : ℕ) = j := rfl

/-- 概要：後半への包含は頂点の番号に切断点を加える。
方針：順序写像の定義を評価する。
規約：KST A.5 の AW。使われ方：面写像との切断公式。 -/
@[simp] lemma awBack_apply (n : ℕ) (i : Fin (n + 1)) (j : Fin (n - (i : ℕ) + 1)) :
    ((awBack n i).toOrderHom j : ℕ) = (i : ℕ) + j := rfl

/-- 概要：AW の第一因子の次数と第二因子の次数は全次数に足し上がる。
方針：切断点 i は n 以下であることを使う。
規約：KST A.5、零次の因子も含む。
使われ方：全テンソルの直和成分への標準包含。 -/
lemma awDegrees (n : ℕ) (i : Fin (n + 1)) :
    ComplexShape.π (.down ℕ) (.down ℕ) (.down ℕ) ((i : ℕ), n - i) = n := by
  change (i : ℕ) + (n - i) = n
  exact Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)

/-- 概要：Alexander–Whitney の各切断点に対応する全テンソルへの写像。
方針：前半と後半の制限のテンソルを直和成分へ入れる。
規約：KST A.5、交代面写像複体での非正規化の成分。
使われ方：切断点の有限和と鎖写像性の検証。 -/
@[kerodon 00S2]
def alexanderWhitneySummand (C D : SimplicialObject (ModuleCat.{u} ℤ))
    (n : ℕ) (i : Fin (n + 1)) :
    (simplicialIntegerTensor C D).obj (op ⦋n⦌) ⟶
      (chainIntegerTensor ((alternatingFaceMapComplex _).obj C)
        ((alternatingFaceMapComplex _).obj D)).X n :=
  integerTensorMap (C.map (awFront n i).op) (D.map (awBack n i).op) ≫
    ιMapBifunctor ((alternatingFaceMapComplex _).obj C)
      ((alternatingFaceMapComplex _).obj D) integerTensorBifunctor (.down ℕ)
      i (n - i) n (awDegrees n i)

/-- 概要：Alexander–Whitney の全次数 n の成分写像。
方針：共有切断点 i=0,…,n について成分の和を取る。
規約：KST Construction A.5 の標準的な AW の公式。
使われ方：鎖写像性と shuffle との標準比較を構成するための実写像。 -/
@[kerodon 00S2]
def alexanderWhitneyApp (C D : SimplicialObject (ModuleCat.{u} ℤ)) (n : ℕ) :
    (simplicialIntegerTensor C D).obj (op ⦋n⦌) ⟶
      (chainIntegerTensor ((alternatingFaceMapComplex _).obj C)
        ((alternatingFaceMapComplex _).obj D)).X n :=
  ∑ i : Fin (n + 1), alexanderWhitneySummand C D n i

/-- 概要：全テンソルの成分包含は二つの鎖写像に自然。
方針：通常の全複体の自然性を明示的なテンソル写像の合成則で整理する。
規約：KST A.5。使われ方：AW の各切断点の自然性。 -/
lemma ι_chainIntegerTensorMap
    {K K' L L' : ChainComplex (ModuleCat.{u} ℤ) ℕ} (f : K ⟶ K') (g : L ⟶ L')
    (i j n : ℕ) (h : ComplexShape.π (.down ℕ) (.down ℕ) (.down ℕ) (i, j) = n) :
    ιMapBifunctor K L integerTensorBifunctor (.down ℕ) i j n h ≫
      (chainIntegerTensorMap f g).f n =
    integerTensorMap (f.f i) (g.f j) ≫
      ιMapBifunctor K' L' integerTensorBifunctor (.down ℕ) i j n h := by
  rw [chainIntegerTensorMap, ι_mapBifunctorMap]
  change integerTensorMap (f.f i) (𝟙 _) ≫ integerTensorMap (𝟙 _) (g.f j) ≫ _ = _
  rw [← Category.assoc, ← integerTensorMap_comp]
  simp only [Category.comp_id, Category.id_comp]

/-- 概要：AW の各切断点の写像は両因子の写像に自然。
方針：前半・後半への制限と入力写像の自然性をテンソルする。
規約：KST A.5、外部作用も同じ自然性の特殊化。
使われ方：AW の標準比較の同変性。 -/
lemma alexanderWhitneySummand_naturality
    {C C' D D' : SimplicialObject (ModuleCat.{u} ℤ)} (f : C ⟶ C') (g : D ⟶ D')
    (n : ℕ) (i : Fin (n + 1)) :
    integerTensorMap (f.app (op ⦋n⦌)) (g.app (op ⦋n⦌)) ≫ alexanderWhitneySummand C' D' n i =
      alexanderWhitneySummand C D n i ≫
        (chainIntegerTensorMap ((alternatingFaceMapComplex _).map f)
          ((alternatingFaceMapComplex _).map g)).f n := by
  dsimp only [alexanderWhitneySummand]
  rw [Category.assoc, ι_chainIntegerTensorMap, ← Category.assoc, ← Category.assoc,
    ← integerTensorMap_comp, ← integerTensorMap_comp]
  congr 1
  exact congrArg₂ integerTensorMap (f.naturality (awFront n i).op).symm
    (g.naturality (awBack n i).op).symm

/-- 概要：AW の次数ごとの成分は二つの単体的整数加群の射に自然。
方針：各切断点の自然性を有限和に移す。
規約：KST A.5、正規化前の標準 AW。
使われ方：正規化された比較の同変性と関手性。 -/
lemma alexanderWhitneyApp_naturality
    {C C' D D' : SimplicialObject (ModuleCat.{u} ℤ)} (f : C ⟶ C') (g : D ⟶ D') (n : ℕ) :
    integerTensorMap (f.app (op ⦋n⦌)) (g.app (op ⦋n⦌)) ≫ alexanderWhitneyApp C' D' n =
      alexanderWhitneyApp C D n ≫
        (chainIntegerTensorMap ((alternatingFaceMapComplex _).map f)
          ((alternatingFaceMapComplex _).map g)).f n := by
  simp only [alexanderWhitneyApp, Preadditive.comp_sum, Preadditive.sum_comp,
    alexanderWhitneySummand_naturality]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.2.3.22" (partial := special) "仮定：二つの整数加群値単体的対象（Lean が強い：一般の n 変数の多重加法関手でなくテンソルの場合）。結論：前面と後面を取り全次数の分割について加える Alexander–Whitney 写像（二変数の場合は一致）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitneySummand
