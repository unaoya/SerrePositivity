module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.Unnormalized
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.NormalizedChains
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.DegeneracyCuts

/-!
# 正規化 Alexander–Whitney 対角の成分

概要：Berger–Fresse §1.1.4 の AW 公式を正規化鎖の各次数に構成する。
方針：非正規化公式の両因子を正規化し、退化の消滅により始域も正規化へ降ろす。
規約：ここでは次数ごとの射を構成し、全成分を束ねた鎖写像の条件は別途証明する。
使われ方：Barratt–Eccles の Hopf 対角の鎖写像を構成する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.SimplicialChains.AlexanderWhitney

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped _root_.Simplicial _root_.TensorProduct

variable (A : Type u) [CommRing A]

/-- 概要：非正規化入力から二つの正規化鎖への AW 成分（Berger–Fresse §1.1.4）。
方針：非正規化 AW 成分の二つの因子に射影を適用する。
規約：入力の次数は n=p+q。
使われ方：退化成分の消滅を示して正規化 AW 成分を得る。 -/
def projectedRawComponent (X : SSet.{0}) (n p q : ℕ) (h : p + q = n) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.simplexModule A X n ⟶ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X p ⊗ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X q :=
  _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.rawComponent A X n p q h ≫ ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.normalization A X).f p ⊗ₘ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.normalization A X).f q)

/-- 概要：両因子を正規化した AW 成分の生成元公式（Berger–Fresse §1.1.4）。
方針：非正規化生成元公式とテンソル射の純テンソルでの評価を使う。
規約：切断された面が退化している場合の生成元も含む。
使われ方：始域の退化が出力で消えることを検査する。 -/
@[simp] lemma projectedRawComponent_freeMk (X : SSet.{0}) (n p q : ℕ)
    (h : p + q = n) (x : X _⦋n⦌) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.projectedRawComponent A X n p q h (ModuleCat.freeMk (ULift.up x)) =
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X p (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x 0 p (by omega)) ⊗ₜ[A]
        _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X q (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x p q (by omega)) := by
  simp only [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.projectedRawComponent, ModuleCat.comp_apply, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.rawComponent_freeMk,
    ModuleCat.MonoidalCategory.tensorHom_tmul, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator]
  rfl

/-- 概要：両因子を正規化した AW 成分は全ての退化写像を消す（Berger–Fresse §1.1.4）。
方針：各退化単体の切断について、非単射な因子の正規化生成元を零にする。
規約：切断点での退化は後半で消すので、p=0 や q=0 も含む。
使われ方：正規化 Moore 成分への降下を保証する。 -/
lemma σ_projectedRawComponent (X : SSet.{0}) (n p q : ℕ)
    (h : p + q = n + 1) (i : Fin (n + 1)) :
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj X).σ i ≫
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.projectedRawComponent A X (n + 1) p q h = 0 := by
  apply ModuleCat.free_hom_ext
  intro ⟨x⟩
  change _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.projectedRawComponent A X (n + 1) p q h
    (((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj X).σ i (ModuleCat.freeMk (ULift.up x))) = 0
  have hs : ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj X).σ i (ModuleCat.freeMk (ULift.up x)) =
      ModuleCat.freeMk (ULift.up (X.σ i x)) := ModuleCat.free_map_apply _ _
  rw [hs, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.projectedRawComponent_freeMk, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut_σ, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut_σ]
  obtain hp | hq := _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.aw_degeneracy_not_mono i p q h
  · rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator_map_of_not_mono A X p _ hp, TensorProduct.zero_tmul]
  · rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator_map_of_not_mono A X q _ hq, TensorProduct.tmul_zero]

/-- 概要：正規化 AW 対角の (p,q) 成分（Berger–Fresse §1.1.4）。
方針：射影済みの非正規化成分を Moore 部分加群へ制限する。
規約：始域と終域の全因子が既存の正規化 Moore 鎖である。
使われ方：鎖写像の条件と Hopf 法則を検査する AW 成分となる。 -/
def component (X : SSet.{0}) (n p q : ℕ) (h : p + q = n) :
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X n ⟶ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X p ⊗ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X q :=
  _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.restrictToNormalized ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj X) n
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.projectedRawComponent A X n p q h)

/-- 概要：正規化 AW 成分を射影に前置すると元の公式を得る（Berger–Fresse §1.1.4）。
方針：退化写像の消滅と正規化への降下補題を適用する。
規約：正規化前の全ての鎖に対する射の等式である。
使われ方：正規化生成元上の AW 公式を導く。 -/
lemma normalization_component (X : SSet.{0}) (n p q : ℕ) (h : p + q = n) :
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.normalization A X).f n ≫ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component A X n p q h = _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.projectedRawComponent A X n p q h := by
  apply _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.normalization_restrictToNormalized
  intro k e i
  cases e
  simpa using _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.σ_projectedRawComponent A X k p q h i

/-- 概要：正規化 AW 成分の生成元公式（Berger–Fresse §1.1.4）。
方針：射の降下等式を自由生成元で評価する。
規約：退化した入力や切断面にも同じ公式が成立する。
使われ方：自然性・余結合性・shuffle 適合性を単体の有限和で検証する。 -/
@[simp] lemma component_generator (X : SSet.{0}) (n p q : ℕ)
    (h : p + q = n) (x : X _⦋n⦌) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component A X n p q h (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X n x) =
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X p (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x 0 p (by omega)) ⊗ₜ[A]
        _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X q (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x p q (by omega)) := by
  have he := congrArg (fun f => f (ModuleCat.freeMk (ULift.up x)))
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.normalization_component A X n p q h)
  exact he.trans (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.projectedRawComponent_freeMk A X n p q h x)

end SerrePositivity.SimplicialChains.AlexanderWhitney
