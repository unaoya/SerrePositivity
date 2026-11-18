module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.ChainDiagonal
public import SerrePositivity.HomologicalAlgebra.Complexes.NegativeTensor.Projections

/-!
# 整数コチェイン模型の Alexander–Whitney 対角

概要：Berger–Fresse §1.1.4 の AW 鎖写像を負の整数コチェイン模型へ移す。
方針：自然数鎖写像を零延長し、延長とテンソルの自然な比較同型を後置する。
規約：Barratt–Eccles の既存の normalizedFunctor と同じ複体を使う。
使われ方：E の Hopf 対角の arity ごとの鎖写像。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.SimplicialChains.AlexanderWhitney

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open scoped _root_.Simplicial _root_.TensorProduct

variable (A : Type u) [CommRing A]

/-- 概要：単体集合の正規化鎖の整数コチェイン模型（Berger–Fresse §1.1）。
方針：既存の正規化関手を使う。
規約：自然数鎖次数 n をコチェイン次数 −n に置く。
使われ方：一般の AW 対角を既存の Barratt–Eccles 複体へ適用する。 -/
abbrev cochains (X : SSet.{0}) : CochainComplex (ModuleCat.{u} A) ℤ :=
  (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj X

/-- 概要：単体集合の射による正規化コチェイン写像（Berger–Fresse §1.1）。
方針：既存の正規化関手の射を使う。
規約：既存の E(n) の置換作用と同じ関手である。
使われ方：整数 AW 対角の自然性を述べる。 -/
abbrev cochainMap {X Y : SSet.{0}} (f : X ⟶ Y) : _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A X ⟶ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A Y :=
  (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map f

/-- 概要：正規化 AW の整数コチェイン対角（Berger–Fresse §1.1.4）。
方針：自然数鎖の対角を延長してテンソル比較の順方向を後置する。
規約：任意の小さい単体集合と可換係数環に適用する。
使われ方：Barratt–Eccles の Hopf 対角の成分を供給する。 -/
def cochainDiagonal (X : SSet.{0}) : _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A X ⟶ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A X ⊗ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A X :=
  extendMap (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal A X) ComplexShape.embeddingDownNat ≫
    (_root_.SerrePositivity.NegativeTensor.comparison (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X)).hom

/-- 概要：整数 AW 対角の負次数での値（Berger–Fresse §1.1.4）。
方針：延長した射とテンソル比較の次数成分を展開する。
規約：入力を自然数鎖へ移してから元の AW 対角を施す。
使われ方：整数対角の切断公式と shuffle 適合性を計算する。 -/
lemma cochainDiagonal_f_neg (X : SSet.{0}) (n : ℕ) :
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal A X).f (-(n : ℤ)) =
      (_root_.SerrePositivity.NegativeTensor.xIso (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) n).hom ≫ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal A X).f n ≫
        _root_.SerrePositivity.NegativeTensor.degreeMap (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) n := by
  simp only [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal, HomologicalComplex.comp_f, _root_.SerrePositivity.NegativeTensor.extendMap_f_neg,
    _root_.SerrePositivity.NegativeTensor.comparison_hom_f_neg, Category.assoc, Iso.inv_hom_id_assoc]

/-- 概要：整数 AW 対角は単体集合の射に自然（Berger–Fresse §1.1.4）。
方針：鎖対角の自然性を延長しテンソル比較の自然性を使う。
規約：既存の正規化コチェイン関手に対する自然性である。
使われ方：E(n) の対角の置換作用との適合性。 -/
lemma cochainDiagonal_natural {X Y : SSet.{0}} (f : X ⟶ Y) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainMap A f ≫ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal A Y =
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal A X ≫ HomologicalComplex.tensorHom (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainMap A f) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainMap A f) := by
  change extendMap (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chainMap A f) ComplexShape.embeddingDownNat ≫
      (extendMap (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal A Y) ComplexShape.embeddingDownNat ≫ _) =
    (extendMap (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal A X) ComplexShape.embeddingDownNat ≫ _) ≫
      HomologicalComplex.tensorHom (extendMap (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chainMap A f) ComplexShape.embeddingDownNat)
        (extendMap (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chainMap A f) ComplexShape.embeddingDownNat)
  rw [← Category.assoc, ← extendMap_comp, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal_natural, extendMap_comp]
  rw [Category.assoc, _root_.SerrePositivity.NegativeTensor.comparison_natural, Category.assoc]

/-- 概要：整数 AW 対角の各二次数成分は元の成分の移送（Berger–Fresse §1.1.4）。
方針：テンソル比較とその逆を消し、自然数鎖の射影公式を使う。
規約：全次数 −n、二次数 −p,−q とする。
使われ方：整数 AW の生成元公式と shuffle の適合性。 -/
@[reassoc (attr := simp)]
lemma cochainDiagonal_projection (X : SSet.{0}) (n p q : ℕ) (h : p + q = n) :
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal A X).f (-(n : ℤ)) ≫
        _root_.SerrePositivity.NegativeTensor.projection (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) n p q h =
      (_root_.SerrePositivity.NegativeTensor.xIso (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) n).hom ≫ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component A X n p q h ≫
        ((_root_.SerrePositivity.NegativeTensor.xIso (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) p).inv ⊗ₘ
          (_root_.SerrePositivity.NegativeTensor.xIso (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) q).inv) := by
  simp only [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal_f_neg, Category.assoc,
    _root_.SerrePositivity.NegativeTensor.degreeMap_projection, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal_projection_assoc]

/-- 概要：整数 AW の生成元の二次数成分は区間切断で与えられる（Berger–Fresse §1.1.4）。
方針：射影した射の公式を生成元で評価し、標準同型とその逆を消す。
規約：入力は正規化した任意の単体で、退化単体も許す。
使われ方：shuffle と AW の余代数射性を純テンソルの有限和で検証する。 -/
lemma cochainDiagonal_projection_generator (X : SSet.{0}) (n p q : ℕ)
    (h : p + q = n) (x : X _⦋n⦌) :
    _root_.SerrePositivity.NegativeTensor.projection (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) n p q h
        ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal A X).f (-(n : ℤ))
          ((_root_.SerrePositivity.NegativeTensor.xIso (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) n).inv (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X n x))) =
      (_root_.SerrePositivity.NegativeTensor.xIso (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) p).inv
          (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X p (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x 0 p (by omega))) ⊗ₜ[A]
        (_root_.SerrePositivity.NegativeTensor.xIso (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) q).inv
          (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X q (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x p q (by omega))) := by
  have he := congrArg (fun φ => (_root_.SerrePositivity.NegativeTensor.xIso (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) n).inv ≫ φ)
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal_projection A X n p q h)
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at he
  have hv := congrArg (fun φ => φ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X n x)) he
  change _root_.SerrePositivity.NegativeTensor.projection (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) n p q h
      ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal A X).f (-(n : ℤ))
        ((_root_.SerrePositivity.NegativeTensor.xIso (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) n).inv (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X n x))) =
    ((_root_.SerrePositivity.NegativeTensor.xIso (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) p).inv ⊗ₘ (_root_.SerrePositivity.NegativeTensor.xIso (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) q).inv)
      (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component A X n p q h (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X n x)) at hv
  simpa only [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component_generator, ModuleCat.MonoidalCategory.tensorHom_tmul] using hv

end SerrePositivity.SimplicialChains.AlexanderWhitney
