module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.Components

/-!
# 正規化 AW 成分の自然性と余単位・余結合性

概要：Berger–Fresse §1.1.4 の AW 公式の自然性と余代数の法則を次数ごとに証明する。
方針：正規化生成元で検査し、切断の自然性と反復切断の公式へ帰着する。
規約：鎖写像として束ねる前の次数成分の等式を述べる。
使われ方：Barratt–Eccles の Hopf 対角の法則と同変性に用いる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.SimplicialChains.AlexanderWhitney

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicTopology _root_.AlgebraicTopology.DoldKan
open scoped _root_.Simplicial _root_.TensorProduct

variable (A : Type u) [CommRing A]

/-- 概要：単体集合の射による正規化鎖写像（Berger–Fresse §1.1.4）。
方針：線形化した射に正規化 Moore 関手を適用する。
規約：自然数の鎖次数を保つ。
使われ方：AW 対角の自然性を記述する。 -/
def chainMap {X Y : SSet.{0}} (f : X ⟶ Y) : _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X ⟶ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A Y :=
  (normalizedMooreComplex (ModuleCat A)).map ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).map f)

/-- 概要：正規化鎖写像は生成元を像の単体の生成元に送る（Berger–Fresse §1.1.4）。
方針：正規化射影の自然性を標準生成元で評価する。
規約：退化する像にも公式が成り立つ。
使われ方：AW 成分の自然性を生成元で計算する。 -/
@[simp] lemma chainMap_generator {X Y : SSet.{0}} (f : X ⟶ Y) (n : ℕ) (x : X _⦋n⦌) :
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chainMap A f).f n (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X n x) = _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A Y n (f.app _ x) := by
  have h := congrArg (fun φ => φ.f n)
    (PInftyToNormalizedMooreComplex_naturality ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).map f))
  have hv := congrArg (fun φ => φ (ModuleCat.freeMk (ULift.up x))) h
  change (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.normalization A Y).f n
      (((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).map f).app _ (ModuleCat.freeMk (ULift.up x))) =
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chainMap A f).f n (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X n x) at hv
  erw [ModuleCat.free_map_apply] at hv
  exact hv.symm

/-- 概要：正規化 AW 成分は単体集合の射に自然（Berger–Fresse §1.1.4）。
方針：生成元上で切断の自然性を二つの因子に使う。
規約：任意の単体集合の射に適用できる。
使われ方：Σ_n 作用と単体的オペラッド合成に対する対角の可換性を与える。 -/
lemma component_natural {X Y : SSet.{0}} (f : X ⟶ Y)
    (n p q : ℕ) (h : p + q = n) :
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chainMap A f).f n ≫ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component A Y n p q h =
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component A X n p q h ≫ ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chainMap A f).f p ⊗ₘ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chainMap A f).f q) := by
  apply _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator_hom_ext A X n
  intro x
  simp only [ModuleCat.comp_apply, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chainMap_generator, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component_generator,
    ModuleCat.MonoidalCategory.tensorHom_tmul, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chainMap_generator]
  rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut_natural f x 0 p (by omega), _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut_natural f x p q (by omega)]

/-- 概要：正規化 AW 成分は三重次数について余結合的（Berger–Fresse §1.1.4）。
方針：反復切断を同じ三つの連続した区間に同定する。
規約：テンソルは結合子で右結合に揃える。
使われ方：鎖写像としての AW 対角の余結合性の各成分となる。 -/
lemma component_coassoc (X : SSet.{0}) (p q r : ℕ) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component A X (p + q + r) (p + q) r rfl ≫
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component A X (p + q) p q rfl ▷ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X r) ≫
        (α_ ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X p) ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X q) ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X r)).hom =
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component A X (p + q + r) p (q + r) (Nat.add_assoc p q r).symm ≫
        ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X p ◁ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component A X (q + r) q r rfl) := by
  apply _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator_hom_ext A X (p + q + r)
  intro x
  simp only [ModuleCat.comp_apply, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component_generator,
    ModuleCat.MonoidalCategory.whiskerRight_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply,
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component_generator, ModuleCat.MonoidalCategory.associator_hom_apply]
  simp only [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut_cut, zero_add, add_zero]

/-- 概要：正規化鎖の次数零の augmentation（Berger–Fresse §1.1.4）。
方針：全ての頂点を単位加群の 1 に送り、Moore 成分へ制限する。
規約：単体集合が空の場合にも定義する。
使われ方：AW 対角の左右の余単位の次数零成分となる。 -/
def vertexAugmentation (X : SSet.{0}) : (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X 0 ⟶ 𝟙_ (ModuleCat A) :=
  _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.restrictToNormalized ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj X) 0
    (ModuleCat.freeDesc (↾fun _ : ULift.{u} (X _⦋0⦌) => (1 : A)))

/-- 概要：頂点の augmentation の値は 1（Berger–Fresse §1.1.4）。
方針：零次では退化条件が空である正規化への降下を使う。
規約：全ての頂点に同じ値を与える。
使われ方：AW 成分の余単位を生成元で計算する。 -/
@[simp] lemma vertexAugmentation_generator (X : SSet.{0}) (x : X _⦋0⦌) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.vertexAugmentation A X (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X 0 x) = (1 : A) := by
  have h := _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.normalization_restrictToNormalized ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj X) 0
    (ModuleCat.freeDesc (M := 𝟙_ (ModuleCat A)) (↾fun _ : ULift.{u} (X _⦋0⦌) => (1 : A)))
    (fun k e _ => by omega)
  have hv := congrArg (fun f => f (ModuleCat.freeMk (ULift.up x))) h
  change _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.vertexAugmentation A X (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X 0 x) =
    ModuleCat.freeDesc (M := 𝟙_ (ModuleCat A))
      (↾fun _ : ULift.{u} (X _⦋0⦌) => (1 : A)) (ModuleCat.freeMk (ULift.up x)) at hv
  erw [ModuleCat.freeDesc_apply] at hv
  exact hv

/-- 概要：正規化 AW 成分の左余単位則（Berger–Fresse §1.1.4）。
方針：前半が零次の場合、後半は全単体への制限である。
規約：左単位子を用いて単位加群の因子を消す。
使われ方：AW 対角と augmentation の左余単位則を与える。 -/
lemma component_left_counit (X : SSet.{0}) (n : ℕ) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component A X n 0 n (by omega) ≫
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.vertexAugmentation A X ▷ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X n) ≫ (λ_ ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X n)).hom =
      𝟙 ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X n) := by
  apply _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator_hom_ext A X n
  intro x
  simp only [ModuleCat.comp_apply, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component_generator,
    ModuleCat.MonoidalCategory.whiskerRight_apply, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.vertexAugmentation_generator,
    ModuleCat.MonoidalCategory.leftUnitor_hom_apply, one_smul, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut_zero, ModuleCat.id_apply]

/-- 概要：正規化 AW 成分の右余単位則（Berger–Fresse §1.1.4）。
方針：後半が零次の場合、前半は全単体への制限である。
規約：右単位子を用いて単位加群の因子を消す。
使われ方：AW 対角と augmentation の右余単位則を与える。 -/
lemma component_right_counit (X : SSet.{0}) (n : ℕ) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component A X n n 0 (by omega) ≫
        ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X n ◁ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.vertexAugmentation A X) ≫ (ρ_ ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X n)).hom =
      𝟙 ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X n) := by
  apply _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator_hom_ext A X n
  intro x
  simp only [ModuleCat.comp_apply, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component_generator,
    ModuleCat.MonoidalCategory.whiskerLeft_apply, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.vertexAugmentation_generator,
    ModuleCat.MonoidalCategory.rightUnitor_hom_apply, one_smul, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut_zero, ModuleCat.id_apply]

end SerrePositivity.SimplicialChains.AlexanderWhitney
