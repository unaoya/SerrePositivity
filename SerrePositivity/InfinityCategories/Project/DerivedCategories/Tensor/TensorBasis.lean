module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.SemifreeBasisEquivalence
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # 複体のテンソル積の次数付き基底

概要：各次数のテンソル積を次数の和ごとの直和に分け、二つの基底の積を移す。
方針：Mathlib のテンソル複体の余積表示と具体的な加群直和を比較する。
規約：テンソル積は直和 totalization。使われ方：semifree テンソル積の高さ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded HomologicalComplex
open scoped DirectSum TensorProduct

/-- 概要：直和基底のベクトルは一つの成分に入れた基底ベクトルである。
方針：表現同型に写し、直和と sigma 添字の有限台関数の同型を使う。
規約：加群と添字の宇宙は任意。使われ方：テンソル複体の基底ベクトルの具体形。 -/
theorem directSumBasis_apply {R : Type u} [CommRing R] {I : Type v} [DecidableEq I]
    {V : I → Type w} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {J : I → Type w} (E : ∀ i, Module.Basis (J i) R (V i)) (a : Σ i, J i) :
    DFinsupp.basis E a = DFinsupp.single a.1 (E a.1 a.2) := by
  classical
  apply (DFinsupp.basis E).repr.injective
  refine ((DFinsupp.basis E).repr_self a).trans ?_
  change Finsupp.single a 1 =
    (sigmaFinsuppLequivDFinsupp R).symm
      (DFinsupp.mapRange (fun i => (E i).repr) (fun i => map_zero _)
        (DFinsupp.single a.1 (E a.1 a.2)))
  simp only [DFinsupp.mapRange_single, Module.Basis.repr_self]
  exact (sigmaFinsuppEquivDFinsupp.symm_apply_apply (Finsupp.single a (1 : R))).symm.trans
    (congrArg sigmaFinsuppEquivDFinsupp.symm (sigmaFinsuppEquivDFinsupp_single a (1 : R)))

variable {S : Type u} [CommRing S] (P Q : Complex S)

/-- 概要：次数 k のテンソル積を構成する二つの次数の組。
方針：和が k である組を部分型にする。
規約：第一成分は左因子。使われ方：テンソルの直和分解の添字。 -/
abbrev TensorDegreeIndex (k : ℤ) := {a : ℤ × ℤ // a.1 + a.2 = k}

/-- 概要：テンソル積の一つの次数を次数の組ごとの具体的な直和へ移す。
方針：加群の余積と直和の標準同型を用いる。
規約：複体のテンソルは Mathlib のもの。使われ方：テンソル基底の移送。 -/
def tensorDegreeEquiv (k : ℤ) : (P ⊗ Q).X k ≃ₗ[S]
    ⨁ a : TensorDegreeIndex k, (P.X a.1.1 ⊗ Q.X a.1.2 : ModuleCat S) :=
  (ModuleCat.coprodIsoDirectSum
    (fun a : TensorDegreeIndex k => P.X a.1.1 ⊗ Q.X a.1.2)).toLinearEquiv

/-- 概要：直和の単一成分の逆像はテンソル複体への標準包含である。
方針：加群の余積と直和の同型の包含公式を評価する。
規約：次数の和の証明を添える。使われ方：基底の微分を計算する。 -/
theorem tensorDegreeEquiv_symm_lof (k : ℤ) (a : TensorDegreeIndex k)
    (x : (P.X a.1.1 ⊗ Q.X a.1.2 : ModuleCat S)) :
    (tensorDegreeEquiv P Q k).symm
      (DirectSum.lof S (TensorDegreeIndex k)
        (fun a => (P.X a.1.1 ⊗ Q.X a.1.2 : ModuleCat S)) a x) =
      (ιTensorObj P Q a.1.1 a.1.2 k a.2).hom x :=
  congrArg (fun f => f.hom x)
    (ModuleCat.lof_coprodIsoDirectSum_inv
      (fun a : TensorDegreeIndex k => P.X a.1.1 ⊗ Q.X a.1.2) a)

namespace ComplexSemifreeBasis
variable {P Q} (B : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis S P) (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis S Q)

/-- 概要：テンソル複体の次数付き基底の添字。
方針：次数の組ごとに左右の基底添字の積を取る。
規約：sigma の第一成分が次数の組。使われ方：高さの和。 -/
abbrev TensorIndex (k : ℤ) :=
  Σ a : TensorDegreeIndex k, B.Index a.1.1 × C.Index a.1.2

/-- 概要：左右の基底のテンソル積を各次数の直和にまとめた基底。
方針：直和基底をテンソル次数同型の逆で移す。
規約：環は任意の可換環。使われ方：テンソル積の semibasis。 -/
def tensorBasis (k : ℤ) : Module.Basis (B.TensorIndex C k) S ((P ⊗ Q).X k) :=
  (DFinsupp.basis (fun a : TensorDegreeIndex k =>
    (B.basis a.1.1).tensorProduct (C.basis a.1.2))).map (tensorDegreeEquiv P Q k).symm

/-- 概要：テンソル基底のベクトルは二つの基底ベクトルの標準包含による像。
方針：直和基底と基底のテンソル積の具体形を使う。
規約：基底添字は左右の組。使われ方：Leibniz 公式の適用。 -/
theorem tensorBasis_apply (k : ℤ) (a : B.TensorIndex C k) :
    B.tensorBasis C k a =
      (ιTensorObj P Q a.1.1.1 a.1.1.2 k a.1.2).hom
        (B.basis a.1.1.1 a.2.1 ⊗ₜ[S] C.basis a.1.1.2 a.2.2) := by
  change (tensorDegreeEquiv P Q k).symm
    (DFinsupp.basis (fun a : TensorDegreeIndex k =>
      (B.basis a.1.1).tensorProduct (C.basis a.1.2)) a) = _
  rw [directSumBasis_apply, Module.Basis.tensorProduct_apply']
  exact tensorDegreeEquiv_symm_lof P Q k a.1 _

/-- 概要：テンソル基底の高さは両因子の高さの和。
方針：次数と基底添字を取り出して加える。
規約：自然数値の高さ。使われ方：両方の微分での厳密下降。 -/
def tensorHeight (k : ℤ) (a : B.TensorIndex C k) : ℕ :=
  B.height a.1.1.1 a.2.1 + C.height a.1.1.2 a.2.2

/-- 概要：指定した高さより低いテンソル基底が張る部分加群。
方針：高さ条件で選んだ基底の線形包を取る。
規約：高さ上限は狭義不等式。使われ方：微分の下降の線形的な判定。 -/
def tensorLowerSpan (k : ℤ) (n : ℕ) : Submodule S ((P ⊗ Q).X k) :=
  Submodule.span S (B.tensorBasis C k '' {a | B.tensorHeight C k a < n})

/-- 概要：左因子の低い高さの線形包をテンソルしても高さの和より低い。
方針：左因子の線形包の帰納法とテンソル基底の包含公式を使う。
規約：右因子は一つの基底ベクトル。使われ方：左微分の高さ下降。 -/
theorem tensor_mem_lowerSpan_left (p q k : ℤ) (h : p + q = k) (n : ℕ)
    (j : C.Index q) (x : P.X p)
    (hx : x ∈ Submodule.span S (B.basis p '' {i | B.height p i < n})) :
    (ιTensorObj P Q p q k h).hom (x ⊗ₜ[S] C.basis q j) ∈
      B.tensorLowerSpan C k (n + C.height q j) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    let a : B.TensorIndex C k := ⟨⟨⟨p, q⟩, h⟩, i, j⟩
    have ha : B.tensorBasis C k a ∈ B.tensorLowerSpan C k (n + C.height q j) :=
      Submodule.subset_span ⟨a, Nat.add_lt_add_right hi _, rfl⟩
    exact (B.tensorBasis_apply C k a) ▸ ha
  | zero =>
    rw [TensorProduct.zero_tmul, map_zero]
    exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
    rw [TensorProduct.add_tmul, map_add]
    exact Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
    rw [← TensorProduct.smul_tmul', map_smul]
    exact Submodule.smul_mem _ a ih

/-- 概要：右因子の低い高さの線形包をテンソルしても高さの和より低い。
方針：右因子の線形包の帰納法とテンソル基底の包含公式を使う。
規約：左因子は一つの基底ベクトル。使われ方：右微分の高さ下降。 -/
theorem tensor_mem_lowerSpan_right (p q k : ℤ) (h : p + q = k) (n : ℕ)
    (i : B.Index p) (y : Q.X q)
    (hy : y ∈ Submodule.span S (C.basis q '' {j | C.height q j < n})) :
    (ιTensorObj P Q p q k h).hom (B.basis p i ⊗ₜ[S] y) ∈
      B.tensorLowerSpan C k (B.height p i + n) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, hj, rfl⟩ := hy
    let a : B.TensorIndex C k := ⟨⟨⟨p, q⟩, h⟩, i, j⟩
    have ha : B.tensorBasis C k a ∈ B.tensorLowerSpan C k (B.height p i + n) :=
      Submodule.subset_span ⟨a, Nat.add_lt_add_left hj _, rfl⟩
    exact (B.tensorBasis_apply C k a) ▸ ha
  | zero =>
    rw [TensorProduct.tmul_zero, map_zero]
    exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
    rw [TensorProduct.tmul_add, map_add]
    exact Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
    rw [TensorProduct.tmul_smul, map_smul]
    exact Submodule.smul_mem _ a ih

end ComplexSemifreeBasis
end SerrePositivity.InfinityCategories.Project.DerivedCategories
