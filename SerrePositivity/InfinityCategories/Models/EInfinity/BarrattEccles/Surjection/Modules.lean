module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Renaming
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
模型。文献の定義との比較は後で
# 全射語で生成される次数成分

概要：Berger–Fresse §1.2.1 の χ(n) の次数 d を非退化全射語上の自由加群で構成する。
方針：任意の語を基底ベクトルへ送り、非全射・退化な語は零へ送る。
規約：基底の添字の宇宙を係数環へ持ち上げる。微分はまだ束ねない。
使われ方：削除微分と table reduction の有限和の値域となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

variable (A : Type u) [CommRing A]

/-- 概要：非退化全射語上の自由加群が χ(n) の次数 d（BF §1.2.1）。
方針：基底の添字を持ち上げて自由加群関手を使う。
規約：整数コチェイン次数 −d への移送は後で行う。
使われ方：surjection オペラッドの複体の次数成分を供給する。 -/
def degreeModule (n d : ℕ) : ModuleCat.{u} A :=
  (ModuleCat.free A).obj (ULift.{u} (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d))

/-- 概要：次数成分の非退化全射語による自由基底（BF §1.2.1）。
方針：有限台関数の標準基底を使う。
規約：添字は係数環の宇宙へ持ち上げる。
使われ方：微分・群作用・部分合成を基底の像から線形に延長する。 -/
def basis (n d : ℕ) : Module.Basis (ULift.{u} (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d)) A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n d) :=
  Finsupp.basisSingleOne

/-- 概要：基底ベクトルは台が一点の有限台関数（BF §1.2.1）。
方針：標準基底の評価公式を使う。
規約：値は 1。
使われ方：線形写像を基底で計算する。 -/
@[simp]
lemma basis_apply {n d : ℕ} (v : ULift.{u} (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n d v = Finsupp.single v 1 :=
  congrFun Finsupp.coe_basisSingleOne v

/-- 概要：任意の語を対応する基底元か零へ送る（BF §1.2.1）。
方針：全射性と非退化性を有限判定して基底ベクトルを選ぶ。
規約：退化または非全射なら必ず零。
使われ方：削除微分と TR を退化項を含む和から定義する。 -/
def generator {n d : ℕ} (v : Fin (n + d) → Fin n) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n d :=
  if h : Function.Surjective v ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate v then
    Finsupp.single (ULift.up ⟨v, h⟩) 1 else 0

/-- 概要：非退化全射語は対応する基底ベクトルへ送られる（BF §1.2.1）。
方針：有限判定の肯定側を評価する。
規約：部分型の証明の違いは無視する。
使われ方：生成元上の写像の公式を証明する。 -/
@[simp]
lemma generator_word {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator A v.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n d (ULift.up v) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator, dite_eq_left v.property]
  exact (congrFun Finsupp.coe_basisSingleOne (ULift.up v)).symm

/-- 概要：非全射な語は零を表す（BF §1.2.1）。
方針：生成元の有限判定の否定側を使う。
規約：隣接値の条件によらない。
使われ方：最後の唯一の出現を削除した微分項を除く。 -/
lemma generator_eq_zero_of_not_surjective {n d : ℕ} (v : Fin (n + d) → Fin n)
    (h : ¬ Function.Surjective v) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator A v = 0 := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator, h, false_and, ↓reduceDIte]

/-- 概要：退化な語は零を表す（BF §1.2.1）。
方針：生成元の有限判定の否定側を使う。
規約：全射性の有無によらない。
使われ方：削除・TR の出力に現れる退化項を除く。 -/
lemma generator_eq_zero_of_not_nondegenerate {n d : ℕ} (v : Fin (n + d) → Fin n)
    (h : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate v) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator A v = 0 := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator, h, and_false, ↓reduceDIte]

/-- 概要：値の置換を次数成分の線形写像へ延長する（BF §1.2.1）。
方針：基底の添字の置換で有限台関数の台を移す。
規約：位置と次数は保つ。
使われ方：χ の対称列の射を作る。 -/
def renameLinear {n d : ℕ} (σ : Equiv.Perm (Fin n)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n d →ₗ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n d :=
  Finsupp.lmapDomain A A (fun v : ULift.{u} (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) =>
    ULift.up (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word.rename σ v.down))

/-- 概要：線形な値の置換は基底の値の置換を延長する（BF §1.2.1）。
方針：台が一点の有限台関数の像を計算する。
規約：共変な左作用。
使われ方：群作用の法則と TR の同変性を基底で検証する。 -/
@[simp]
lemma renameLinear_basis {n d : ℕ} (σ : Equiv.Perm (Fin n)) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.renameLinear A σ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n d (ULift.up v)) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n d (ULift.up (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word.rename σ v)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis_apply, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis_apply]
  exact Finsupp.mapDomain_single

/-- 概要：値の置換は任意の語の基底か零への正規化と可換（BF §1.2.1）。
方針：有効な語では基底公式を使い、無効な語では判定の同値で両辺を零にする。
規約：非全射・退化な語も含む。
使われ方：削除微分の同変性を項ごとに証明する。 -/
lemma renameLinear_generator {n d : ℕ} (σ : Equiv.Perm (Fin n))
    (v : Fin (n + d) → Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.renameLinear A σ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator A v) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator A (σ ∘ v) := by
  by_cases h : Function.Surjective v ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate v
  · rw [show _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator A v = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n d (ULift.up ⟨v, h⟩) from _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator_word A ⟨v, h⟩,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.renameLinear_basis]
    exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator_word A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word.rename σ ⟨v, h⟩)).symm
  · have h' : ¬ (Function.Surjective (σ ∘ v) ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate (σ ∘ v)) := by
      simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.surjective_rename_iff, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.nondegenerate_rename_iff] using h
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator, dite_eq_right h, dite_eq_right h', map_zero]

/-- 概要：単位置換は次数成分上で恒等線形写像（BF §1.2.1）。
方針：自由基底の各元で値を比較する。
規約：arity 0 も含む。
使われ方：対称群の線形表現の単位則を与える。 -/
@[simp]
lemma renameLinear_one (n d : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.renameLinear A (1 : Equiv.Perm (Fin n)) =
      (LinearMap.id : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n d →ₗ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n d) := by
  apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n d).ext
  intro v
  obtain ⟨v⟩ := v
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.renameLinear_basis, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word.rename_one, LinearMap.id_apply]

/-- 概要：値の置換の積は線形写像の合成を保つ（BF §1.2.1）。
方針：自由基底で語の置換の合成則を使う。
規約：先に τ、次に σ を作用させる。
使われ方：対称群の線形表現の積の法則を与える。 -/
lemma renameLinear_mul {n d : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.renameLinear A (σ * τ) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.renameLinear A σ).comp (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.renameLinear A τ : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n d →ₗ[A] _) := by
  apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n d).ext
  intro v
  obtain ⟨v⟩ := v
  simp only [LinearMap.comp_apply, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.renameLinear_basis, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word.rename_mul]

/-- 概要：次数成分上の対称群の線形表現（BF §1.2.1）。
方針：値の置換の線形延長を単位・積の保存と束ねる。
規約：共変な左作用。
使われ方：χ の対称列とその微分を構成する。 -/
def representation (n d : ℕ) : Equiv.Perm (Fin n) →* Module.End A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n d) where
  toFun := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.renameLinear A
  map_one' := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.renameLinear_one A n d
  map_mul' σ τ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.renameLinear_mul A σ τ

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
