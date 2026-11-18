module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.NormalizationDescent
public import SerrePositivity.EInfinity.BarrattEccles.Normalized

/-!
# 単体集合の正規化鎖の生成元

概要：Berger–Fresse §1.1.4 の AW 公式に使う正規化鎖の生成元と自然性を整備する。
方針：既存の線形化関手と Dold–Kan の射影を、一般の単体集合について使う。
規約：Barratt–Eccles の既存の自然数鎖複体と定義的に一致する表現を保つ。
使われ方：AW 成分の正規化への降下と、生成元による射の比較に用いる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.SimplicialChains.AlexanderWhitney

open _root_.CategoryTheory _root_.AlgebraicTopology _root_.AlgebraicTopology.DoldKan
open scoped _root_.Simplicial

variable (A : Type u) [CommRing A]

/-- 概要：単体集合の正規化鎖複体（Berger–Fresse §1.1.4）。
方針：自由加群化後に正規化 Moore 関手を適用する。
規約：自然数の鎖次数を用い、微分は一つ下がる。
使われ方：一般の単体集合に対する AW 対角の入力となる。 -/
abbrev chains (X : SSet.{0}) : ChainComplex (ModuleCat A) ℕ :=
  (normalizedMooreComplex (ModuleCat A)).obj ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj X)

/-- 概要：非正規化鎖から正規化鎖への射影（Berger–Fresse §1.1.4）。
方針：Dold–Kan の P∞ の因子化を使う。
規約：Barratt–Eccles に特殊化すると既存の normalizationMap に一致する。
使われ方：任意の単体から正規化生成元を得る。 -/
def normalization (X : SSet.{0}) :
    (alternatingFaceMapComplex (ModuleCat A)).obj ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj X) ⟶
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X := PInftyToNormalizedMooreComplex _

/-- 概要：単体が表す正規化鎖の生成元（Berger–Fresse §1.1.4）。
方針：自由加群の標準生成元に正規化射影を適用する。
規約：退化単体を許し、その場合の生成元は零となる。
使われ方：AW 公式を単体で記述する。 -/
def generator (X : SSet.{0}) (n : ℕ) (x : X _⦋n⦌) : (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X n :=
  (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.normalization A X).f n (ModuleCat.freeMk (ULift.up x))

/-- 概要：正規化射影は非単射な単体圏の射から来る退化を消す（Berger–Fresse §1.1.4）。
方針：Moore 部分加群への包含を後置し、P∞ に対する退化消滅を使う。
規約：標準の一段の退化だけでなく任意の非単射を扱う。
使われ方：切断の中に残った退化を正規化後に消去する。 -/
lemma degeneracy_normalization (X : SSet.{0}) (n : ℕ) {Δ : SimplexCategory}
    (θ : ⦋n⦌ ⟶ Δ) (hθ : ¬Mono θ) :
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj X).map θ.op ≫ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.normalization A X).f n = 0 := by
  let L := (_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj X
  apply (cancel_mono (NormalizedMooreComplex.objX L n).arrow).1
  have hp := congrArg (fun f => f.f n)
    (PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap L)
  change (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.normalization A X).f n ≫ (NormalizedMooreComplex.objX L n).arrow = PInfty.f n at hp
  rw [Category.assoc, hp, degeneracy_comp_PInfty L n θ hθ, Limits.zero_comp]

/-- 概要：非単射な単体圏の射による像の正規化生成元は零（Berger–Fresse §1.1.4）。
方針：退化写像と射影の合成の消滅を標準生成元で評価する。
規約：入力の単体の次数は θ の終域により決まる。
使われ方：AW 成分の退化項を生成元で消す。 -/
lemma generator_map_of_not_mono (X : SSet.{0}) (n : ℕ) {Δ : SimplexCategory}
    (θ : ⦋n⦌ ⟶ Δ) (hθ : ¬Mono θ) (x : X.obj (Opposite.op Δ)) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X n (X.map θ.op x) = 0 := by
  have hv := congrArg (fun f => f (ModuleCat.freeMk (ULift.up x)))
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.degeneracy_normalization A X n θ hθ)
  change (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.normalization A X).f n
    (((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj X).map θ.op (ModuleCat.freeMk (ULift.up x))) = 0 at hv
  erw [ModuleCat.free_map_apply] at hv
  exact hv

/-- 概要：正規化生成元による射の外延性（Berger–Fresse §1.1.4）。
方針：射影を前置して自由生成元で検査し、Moore 包含がその切断であることを使う。
規約：終域は任意の A 加群でよい。
使われ方：AW 成分の自然性と余結合性を生成元で証明する。 -/
lemma generator_hom_ext (X : SSet.{0}) (n : ℕ) {Z : ModuleCat A}
    {f g : (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X n ⟶ Z}
    (h : ∀ x : X _⦋n⦌, f (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X n x) = g (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X n x)) : f = g := by
  have he : (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.normalization A X).f n ≫ f = (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.normalization A X).f n ≫ g := by
    apply ModuleCat.free_hom_ext
    intro ⟨x⟩
    exact h x
  have hs := congrArg (fun φ => φ.f n)
    (splitMonoInclusionOfMooreComplexMap ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj X)).id
  change (inclusionOfMooreComplexMap _).f n ≫ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.normalization A X).f n = 𝟙 _ at hs
  have he' := congrArg (fun φ => (inclusionOfMooreComplexMap _).f n ≫ φ) he
  simpa only [← Category.assoc, hs, Category.id_comp] using he'

end SerrePositivity.SimplicialChains.AlexanderWhitney

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.2.3.10" (partial := component) "仮定：単体集合と係数（HA の ℤ を取れる。own の正規化は小さい単体集合）。結論：自由加群の交代面写像複体と、own の退化を消去した正規化複体がある。HA の Moore 正規化と退化商の比較を採用した型は明示しない（Lean が弱い）。"] _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains
