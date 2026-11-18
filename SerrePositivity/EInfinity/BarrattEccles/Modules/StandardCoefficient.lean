module

public import SerrePositivity.EInfinity.BarrattEccles.HomologyComposition

/-!
# 標準零単体による Barratt–Eccles の結合的係数

概要：Berger–Fresse §1.1.1–1.1.3 の恒等置換の零単体を各 arity で指定する。
方針：正規化生成元を零次サイクルとして単位複体からの射へ移す。
規約：arity 0 を含み、可換 dg 代数への忘却は要求しない。
使われ方：同じ台を持つ結合的 dg 代数の単位と積の係数。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
open scoped Simplicial

/-- 概要：恒等置換一個の標準零単体（Berger–Fresse §1.1.1）。
方針：頂点列との同値を逆向きに使う。規約：空の入力集合も許す。
使われ方：結合的係数の全 arity の指定。 -/
def standardSimplex (n : ℕ) : (simplicial n) _⦋0⦌ :=
  (simplexEquiv n 0).symm (fun _ => 1)

/-- 概要：標準零単体の唯一の頂点は恒等置換（Berger–Fresse §1.1.1）。
方針：頂点列同値の往復。規約：任意の arity。
使われ方：標準係数の部分合成の計算。 -/
@[simp] lemma simplexEquiv_standardSimplex (n : ℕ) (k : Fin 1) :
    simplexEquiv n 0 (standardSimplex n) k = 1 :=
  congrFun ((simplexEquiv n 0).apply_symm_apply (fun _ => 1)) k

variable (A : Type u) [CommRing A]

/-- 概要：標準零単体の正規化生成元はサイクル（Berger–Fresse §1.1.2）。
方針：正次数成分の消滅。規約：元の非正コチェイン複体。
使われ方：単位複体からの係数射。 -/
def standardCoefficientCycle (n : ℕ) : complexCycles A (complex A n) 0 :=
  ⟨(complexXIso A n 0).inv (normalizedGenerator A n 0 (standardSimplex n)),
    complex_eq_zero_of_positive A n 1 (by decide) _⟩

/-- 概要：標準零単体を表す厳密な係数射（Berger–Fresse §1.1.3）。
方針：零次サイクルから単一成分複体の射を作る。
規約：対称群不変性は主張しない。使われ方：結合的忘却の単位・積。 -/
def standardCoefficient (n : ℕ) : 𝟙_ (Complex A) ⟶ (operad A).arity n :=
  complexSphereMap A 0 (standardCoefficientCycle A n)

/-- 概要：arity 1 の標準係数は operad の単位（Berger–Fresse §1.1.3）。
方針：同じ零単体とサイクルを使う定義を比較。
規約：複体の射の等式。使われ方：厳密な単位則。 -/
lemma standardCoefficient_unit : standardCoefficient A 1 = (operad A).unit := rfl

/-- 概要：標準係数の零次成分は標準生成元のスカラー倍（Berger–Fresse §1.1.2）。
方針：単一成分複体の射の成分公式。
規約：任意のスカラー。使われ方：部分合成の厳密計算。 -/
lemma standardCoefficient_zero_apply (n : ℕ) (a : A) :
    (standardCoefficient A n).f 0
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv a) =
    a • (complexXIso A n 0).inv (normalizedGenerator A n 0 (standardSimplex n)) := by
  have h : (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv ≫
      (standardCoefficient A n).f 0 =
      moduleElementMap A ((complex A n).X 0) (standardCoefficientCycle A n).val := by
    dsimp only [standardCoefficient, complexSphereMap]
    rw [mkHomFromSingle_f, Iso.inv_hom_id_assoc]
    rfl
  exact congrArg (fun f => f a) h

/-- 概要：標準零単体どうしの shuffle 合成は標準零単体（Berger–Fresse §1.1.3）。
方針：各頂点の内側・外側置換がともに恒等であることを計算。
規約：零 arity の挿入を含む。使われ方：係数の厳密な部分合成。 -/
lemma shuffleSimplex_standard (m n : ℕ) (i : Fin (m + 1)) (s : ShufflePath 0 0) :
    shuffleSimplex m n i s (standardSimplex (m+1)) (standardSimplex n) =
      standardSimplex (m+n) := by
  apply (simplexEquiv (m+n) 0).injective
  funext k
  rw [simplexEquiv_standardSimplex]
  have h := simplexEquiv_shuffleSimplex m n i s
    (standardSimplex (m+1)) (standardSimplex n) k
  simpa only [simplexEquiv_standardSimplex, permutationComposition,
    outerPermutation_one, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation_one, mul_one] using h

/-- 概要：零次の標準生成元の shuffle は標準生成元（Berger–Fresse §1.1.3）。
方針：唯一の零次経路と符号一で和を評価する。
規約：任意の挿入位置。使われ方：標準係数の積の成分計算。 -/
lemma shuffleBilinear_standard (m n : ℕ) (i : Fin (m + 1)) :
    shuffleBilinear A m n i 0 0
      (normalizedGenerator A (m+1) 0 (standardSimplex (m+1)))
      (normalizedGenerator A n 0 (standardSimplex n)) =
      normalizedGenerator A (m+n) 0 (standardSimplex (m+n)) := by
  let _ : Unique (ShufflePath 0 0) := {
    default := zeroLeftPath 0
    uniq := fun s => s.leftZero_unique (zeroLeftPath 0) }
  rw [shuffleBilinear_generators]
  simp only [shuffleValue, Fintype.sum_unique, ShufflePath.sign_leftZero,
    Units.val_one, one_smul, shuffleSimplex_standard]

/-- 概要：標準係数の全ての部分合成は標準係数（Berger–Fresse §1.1.3）。
方針：単位からの射を零次の一の像で判定し、零次 shuffle を計算する。
規約：零 arity の挿入も含む厳密な等式。使われ方：結合的 dg 代数への忘却。 -/
lemma standardCoefficient_composite (m n : ℕ) (i : Fin (m + 1)) :
    coefficientComposite m n i (standardCoefficient A (m+1))
      (standardCoefficient A n) = standardCoefficient A (m+n) := by
  apply (complexSphereHomEquiv A _ 0).injective
  apply Subtype.ext
  change (partialComposition A m n i).f 0
    ((((λ_ (𝟙_ (Complex A))).inv ≫
      (standardCoefficient A (m+1) ⊗ₘ standardCoefficient A n)).f 0) (1 : A)) =
      (standardCoefficient A (m+n)).f 0 (1 : A)
  rw [unit_tensor_apply]
  have hc (r : ℕ) : (cycleFromUnit _ (standardCoefficient A r)).val =
      (complexXIso A r 0).inv (normalizedGenerator A r 0 (standardSimplex r)) := by
    change (standardCoefficient A r).f 0
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)) = _
    rw [standardCoefficient_zero_apply, one_smul]
  rw [hc, hc]
  erw [partialComposition_neg_tmul A m n i 0 0]
  simp only [Iso.inv_hom_id_apply, shuffleBilinear_standard]
  change (complexXIso A (m+n) 0).inv
    (normalizedGenerator A (m+n) 0 (standardSimplex (m+n))) =
    (standardCoefficient A (m+n)).f 0
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A))
  rw [standardCoefficient_zero_apply, one_smul]

end SerrePositivity.EInfinity.BarrattEccles
