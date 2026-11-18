module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurTensorMorphisms

/-!
模型。文献の定義との比較は後で
# arity 族で指定した演算の Schur テンソルからの降下

概要：Berger–Moerdijk §1 の自由代数の演算を、入力ごとの coinvariant 関係から降ろす。
方針：arity 族を全ての図式の対象へ延長し、自己射の置換に関する不変性を余錐の自然性に変える。
規約：底の係数複体は左に固定する。作用の結合則や単位則は仮定しない。
使われ方：全入力への合成で与えた生成射から Schur 対象上の実際の作用射を構成する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

/-- 概要：対象の型の同値に沿って射族を全対象へ延長する（Berger–Moerdijk §1）。
方針：同値の逆像で射を評価し、始域を等式の射で移す。
規約：添字の型の同値のみを使い、自己射の情報を捨てない。
使われ方：arity 族で指定した射を Schur テンソル図式の全対象へ延長する。 -/
def indexFamilyExtend {I J : Type} (e : I ≃ J) (D : J → Complex A) (C Y : Complex A)
    (f : ∀ i, C ⊗ D (e i) ⟶ Y) (j : J) : C ⊗ D j ⟶ Y :=
  eqToHom (congrArg (fun j => C ⊗ D j) (e.apply_symm_apply j).symm) ≫ f (e.symm j)

private lemma eqToHom_family {I : Type} (D : I → Complex A) (Y : Complex A)
    (f : ∀ i, D i ⟶ Y) {i j : I} (h : i = j) :
    eqToHom (congrArg D h) ≫ f j = f i := by
  subst j
  exact Category.id_comp _

/-- 概要：同値に沿って延長した射族は元の添字で元の射に一致する（Berger–Moerdijk §1）。
方針：同値の逆律で移送を簡約する。
規約：対象の比較の選択には依存しない。
使われ方：Schur テンソルの降下射の生成射上の式を得る。 -/
lemma indexFamilyExtend_apply {I J : Type} (e : I ≃ J) (D : J → Complex A) (C Y : Complex A)
    (f : ∀ i, C ⊗ D (e i) ⟶ Y) (i : I) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.indexFamilyExtend e D C Y f (e i) = f i := by
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.eqToHom_family (fun i => C ⊗ D (e i)) Y f (e.symm_apply_apply i).symm

/-- 概要：arity 族で指定した射を Schur テンソル図式の全対象へ延長する（Berger–Moerdijk §1）。
方針：各対象をその arity 族の標準対象へ戻し、対象の比較の射を前置する。
規約：全対象の arity 族は標準有限集合の濃度で一意に決まる。
使われ方：入力の置換に関する不変性から余錐を作る。 -/
def schurTensorArityFamily (P : _root_.SerrePositivity.SymmetricSequence (Complex A)) (K C Y : Complex A) (n : ℕ)
    (f : ∀ s : Fin n → ℕ, C ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n
      (fun i => _root_.SerrePositivity.SymmetricSequence.level P (s i) ⊗ power K (s i)) ⟶ Y)
    (j : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndex _root_.SerrePositivity.FiniteBijection n) : C ⊗ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorDiagram P K n).obj j ⟶ Y :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.indexFamilyExtend (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorArityEquiv n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorDiagram P K n).obj C Y
    (fun s => (C ◁ eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorDiagram_obj_ofArity P K n s)) ≫ f s) j

/-- 概要：全対象への延長は標準の arity 族で元の射に一致する（Berger–Moerdijk §1）。
方針：arity 族と対象の間の同値の逆律で移送を簡約する。
規約：図式の対象と有限テンソル族の比較の射を残す。
使われ方：降下した作用の生成射上の値を計算する。 -/
lemma schurTensorArityFamily_ofArity (P : _root_.SerrePositivity.SymmetricSequence (Complex A)) (K C Y : Complex A)
    (n : ℕ) (f : ∀ s : Fin n → ℕ, C ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n
      (fun i => _root_.SerrePositivity.SymmetricSequence.level P (s i) ⊗ power K (s i)) ⟶ Y) (s : Fin n → ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorArityFamily P K C Y n f (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorArityEquiv n s) =
      (C ◁ eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorDiagram_obj_ofArity P K n s)) ≫ f s := by
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.indexFamilyExtend_apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorArityEquiv n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorDiagram P K n).obj C Y _ s

/-- 概要：各入力の同時置換に不変な射族は Schur テンソル図式上で自然である（Berger–Moerdijk §1）。
方針：図式の射が arity を変えないことを使い、各自己射を入力ごとの置換に書き換える。
規約：各入力の係数とテンソル冪を同じ置換で動かす。
使われ方：Schur テンソルの余極限の降下に必要な自然性を与える。 -/
lemma schurTensorArityFamily_naturality (P : _root_.SerrePositivity.SymmetricSequence (Complex A)) (K C Y : Complex A)
    (n : ℕ) (f : ∀ s : Fin n → ℕ, C ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n
      (fun i => _root_.SerrePositivity.SymmetricSequence.level P (s i) ⊗ power K (s i)) ⟶ Y)
    (hf : ∀ (s : Fin n → ℕ) (τ : ∀ i, Equiv.Perm (Fin (s i))),
      (C ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i =>
        P.map (_root_.SerrePositivity.FiniteBijection.permutation (s i) (τ i)) ⊗ₘ
          (permutationAction K (s i) (τ i)).asIso.hom)) ≫ f s = f s)
    {j k : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndex _root_.SerrePositivity.FiniteBijection n} (σ : j ⟶ k) :
    (C ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorDiagram P K n).map σ) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorArityFamily P K C Y n f k =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorArityFamily P K C Y n f j := by
  have hjk := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndex_object_eq_of_hom (fun σ => _root_.SerrePositivity.FiniteBijection.object_eq_of_hom σ) n σ
  subst k
  obtain ⟨s, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorArityEquiv n).surjective j
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorArityFamily_ofArity]
  rw [← whiskerLeft_comp_assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorDiagram_map_ofArity]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [hf]

/-- 概要：入力ごとの同時置換に不変な arity 族の射を Schur テンソル冪からの射へ降ろす（Berger–Moerdijk §1）。
方針：全対象に延長した射族の自然性を使い、固定係数付きの余極限の普遍性を適用する。
規約：空の入力族と零入力の演算を含める。
使われ方：自由代数の作用射を全入力への合成の生成射から構成する。 -/
def schurTensorArityDesc (P : _root_.SerrePositivity.SymmetricSequence (Complex A)) (K C Y : Complex A) (n : ℕ)
    (f : ∀ s : Fin n → ℕ, C ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n
      (fun i => _root_.SerrePositivity.SymmetricSequence.level P (s i) ⊗ power K (s i)) ⟶ Y)
    (hf : ∀ (s : Fin n → ℕ) (τ : ∀ i, Equiv.Perm (Fin (s i))),
      (C ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i =>
        P.map (_root_.SerrePositivity.FiniteBijection.permutation (s i) (τ i)) ⊗ₘ
          (permutationAction K (s i) (τ i)).asIso.hom)) ≫ f s = f s) :
    C ⊗ power ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P).obj K) n ⟶ Y :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorDesc P K C Y n (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorArityFamily P K C Y n f)
    (fun σ => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorArityFamily_naturality P K C Y n f hf σ)

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
