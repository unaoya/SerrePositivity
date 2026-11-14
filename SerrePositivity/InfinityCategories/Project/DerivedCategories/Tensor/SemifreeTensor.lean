module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.TensorBasis

/-! # Semifree 複体のテンソル積による閉性

概要：二つの semifree 複体のテンソル積は semifree である。
方針：基底の高さの和を使い、Leibniz 微分の各項が高さを下げることを示す。
規約：有界性・有限性・平坦性の仮定なし。使われ方：導来 ∞ 圏のテンソル積のモデル。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded HomologicalComplex
open scoped TensorProduct
variable {S : Type u} [CommRing S] (P Q : Complex S)

/-- 概要：テンソル複体の微分を一つの次数成分上で表す。
方針：total 微分の二項分解と各方向の微分公式を使う。
規約：符号は Mathlib の total complex の単元値の符号を保持する。
使われ方：基底ベクトルの微分の高さ判定。 -/
theorem tensor_summand_d (p q k : ℤ) (h : p + q = k) :
    ιTensorObj P Q p q k h ≫ (P ⊗ Q).d k (k + 1) =
      ComplexShape.ε₁ (.up ℤ) (.up ℤ) (.up ℤ) (p, q) •
        ((P.d p (p + 1) ▷ Q.X q) ≫ ιTensorObj P Q (p + 1) q (k + 1) (by omega)) +
      ComplexShape.ε₂ (.up ℤ) (.up ℤ) (.up ℤ) (p, q) •
        ((P.X p ◁ Q.d q (q + 1)) ≫ ιTensorObj P Q p (q + 1) (k + 1) (by omega)) := by
  change ιMapBifunctor P Q (curriedTensor (ModuleCat S)) (.up ℤ) p q k h ≫
    (mapBifunctor P Q (curriedTensor (ModuleCat S)) (.up ℤ)).d k (k + 1) = _
  rw [mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
    mapBifunctor.d₁_eq P Q (curriedTensor (ModuleCat S)) (.up ℤ)
      (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl) q (k + 1) (by dsimp; omega),
    mapBifunctor.d₂_eq P Q (curriedTensor (ModuleCat S)) (.up ℤ) p
      (show (ComplexShape.up ℤ).Rel q (q + 1) from rfl) (k + 1) (by dsimp; omega)]
  rfl

/-- 概要：単純テンソルの微分は左右の微分の包含の符号付き和。
方針：成分上の射の等式を元で評価する。
規約：整数単元の作用はその整数値による作用に直す。
使われ方：線形包が微分を含むことの証明。 -/
theorem tensor_summand_d_apply (p q k : ℤ) (h : p + q = k) (x : P.X p) (y : Q.X q) :
    ((P ⊗ Q).d k (k + 1)).hom ((ιTensorObj P Q p q k h).hom (x ⊗ₜ[S] y)) =
      (ComplexShape.ε₁ (.up ℤ) (.up ℤ) (.up ℤ) (p, q) : ℤ) •
        (ιTensorObj P Q (p + 1) q (k + 1) (by omega)).hom
          ((P.d p (p + 1)).hom x ⊗ₜ[S] y) +
      (ComplexShape.ε₂ (.up ℤ) (.up ℤ) (.up ℤ) (p, q) : ℤ) •
        (ιTensorObj P Q p (q + 1) (k + 1) (by omega)).hom
          (x ⊗ₜ[S] (Q.d q (q + 1)).hom y) := by
  have h := congrArg (fun f => f.hom (x ⊗ₜ[S] y)) (tensor_summand_d P Q p q k h)
  simp only [Units.smul_def, ModuleCat.hom_add, LinearMap.add_apply,
    ModuleCat.hom_smul, LinearMap.smul_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply] at h
  exact h

namespace ComplexSemifreeBasis
variable {P Q} (B : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis S P) (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis S Q)

/-- 概要：テンソル基底の微分はその基底より低い高さの線形包に入る。
方針：左右の semibasis の下降則を線形包へ直し、Leibniz の二項に適用する。
規約：高さは両因子の高さの和。使われ方：テンソル積の semibasis 条件。 -/
theorem tensorBasis_d_mem_lowerSpan (k : ℤ) (a : B.TensorIndex C k) :
    ((P ⊗ Q).d k (k + 1)).hom (B.tensorBasis C k a) ∈
      B.tensorLowerSpan C (k + 1) (B.tensorHeight C k a) := by
  rcases a with ⟨⟨⟨p, q⟩, h⟩, i, j⟩
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis.tensorBasis_apply, tensor_summand_d_apply]
  have hx : (P.d p (p + 1)).hom (B.basis p i) ∈
      Submodule.span S (B.basis (p + 1) '' {i' | B.height (p + 1) i' < B.height p i}) :=
    (B.basis (p + 1)).mem_span_image.mpr (fun i' hi' => B.lowering p i i' hi')
  have hy : (Q.d q (q + 1)).hom (C.basis q j) ∈
      Submodule.span S (C.basis (q + 1) '' {j' | C.height (q + 1) j' < C.height q j}) :=
    (C.basis (q + 1)).mem_span_image.mpr (fun j' hj' => C.lowering q j j' hj')
  exact Submodule.add_mem _
    (Submodule.smul_of_tower_mem _ _ (B.tensor_mem_lowerSpan_left C (p + 1) q (k + 1)
      (by omega) (B.height p i) j _ hx))
    (Submodule.smul_of_tower_mem _ _ (B.tensor_mem_lowerSpan_right C p (q + 1) (k + 1)
      (by omega) (C.height q j) i _ hy))

/-- 概要：二つの semibasis からテンソル積の semibasis を構成する。
方針：高さの和と微分の線形包への所属を基底展開の台の下降へ変換する。
規約：任意の可換環と任意の非有界複体。使われ方：既存 semifree 性の保存。 -/
def tensor : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis S (P ⊗ Q) where
  Index := B.TensorIndex C
  basis := B.tensorBasis C
  height := B.tensorHeight C
  lowering k a _b hb :=
    (B.tensorBasis C (k + 1)).mem_span_image.mp
      (B.tensorBasis_d_mem_lowerSpan C k a) hb

end ComplexSemifreeBasis

/-- 概要：semifree 複体どうしのテンソル積は semifree である。
方針：既存 filtration と semibasis の同値を使い、テンソル基底から filtration を得る。
規約：有界性・有限性・平坦性の追加仮定なし。使われ方：D(S) のテンソル構造の対象条件。 -/
theorem complexSemifree_tensor (hP : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S P) (hQ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S Q) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S (P ⊗ Q) := by
  obtain ⟨B⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_nonempty_basis hP
  obtain ⟨C⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_nonempty_basis hQ
  exact (B.tensor C).complexSemifree

end SerrePositivity.InfinityCategories.Project.DerivedCategories
