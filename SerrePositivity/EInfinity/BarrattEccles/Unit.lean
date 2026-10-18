module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleChainMap
public import SerrePositivity.DifferentialGraded.Complexes.Cells

/-!
# Barratt–Eccles の単位演算

概要：Berger–Fresse §1.1.1、§1.1.3 の arity 1 の単位を複体の射として定義する。
方針：一つの恒等置換からなる0単体の正規化生成元を0次のサイクルとして使う。
規約：定義域は既存のコチェインテンソルの単位複体である。
使われ方：Barratt–Eccles オペラッドの unit と左右の単位則に用いる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
open scoped Simplicial

/-- 概要：arity 1 の恒等置換を表す0単体（Berger–Fresse §1.1.1）。
方針：一つの恒等置換からなる頂点列を単体へ戻す。
規約：単体次数は0、arity は1である。
使われ方：単位演算の正規化生成元を与える。 -/
def unitSimplex : (simplicial 1) _⦋0⦌ := (simplexEquiv 1 0).symm (fun _ => 1)

/-- 概要：単位単体の唯一の頂点は恒等置換である（Berger–Fresse §1.1.1）。
方針：単体と頂点列の同値の往復を消去する。
規約：唯一の頂点を任意の Fin 1 の値で指定してよい。
使われ方：部分合成の単位則を頂点ごとに検証する。 -/
@[simp] lemma simplexEquiv_unitSimplex (k : Fin 1) : simplexEquiv 1 0 unitSimplex k = 1 :=
  congrFun ((simplexEquiv 1 0).apply_symm_apply (fun _ => 1)) k

variable (A : Type u) [CommRing A]

/-- 概要：単位単体の0次コチェインはサイクルである（Berger–Fresse §1.1.2）。
方針：1次の成分が零であることを使う。
規約：正規化鎖の0次からコチェイン次数0へ標準同型で戻す。
使われ方：単位複体からの射を作る。 -/
def unitCycle : complexCycles A (complex A 1) 0 :=
  ⟨(complexXIso A 1 0).inv (normalizedGenerator A 1 0 unitSimplex),
    complex_eq_zero_of_positive A 1 1 (by decide) _⟩

/-- 概要：Barratt–Eccles の単位の複体の射（Berger–Fresse §1.1.3）。
方針：単位サイクルを既存の単一成分複体の普遍性で射へ直す。
規約：定義域のテンソル単位は0次に A を持つ。
使われ方：オペラッドの unit のデータとなる。 -/
def unit : 𝟙_ (Complex A) ⟶ complex A 1 := complexSphereMap A 0 (unitCycle A)

/-- 概要：単位の射は0次でスカラーを単位生成元のスカラー倍へ送る（Berger–Fresse §1.1.3）。
方針：単一成分複体の射の成分公式と加群の元からの線形写像を使う。
規約：単位複体の0次の元は singleObjXSelf の逆同型によって A から指定する。
使われ方：部分合成の単位則を純粋テンソルで計算する。 -/
lemma unit_zero_apply (a : A) :
    (unit A).f 0 ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv a) =
      a • (complexXIso A 1 0).inv (normalizedGenerator A 1 0 unitSimplex) := by
  have h : (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv ≫ (unit A).f 0 =
      moduleElementMap A ((complex A 1).X 0) (unitCycle A).val := by
    dsimp only [unit, complexSphereMap]
    rw [mkHomFromSingle_f, Iso.inv_hom_id_assoc]
  exact congrArg (fun f => f a) h

end SerrePositivity.EInfinity.BarrattEccles
