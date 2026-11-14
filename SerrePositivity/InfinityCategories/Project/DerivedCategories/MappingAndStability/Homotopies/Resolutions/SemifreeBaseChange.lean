module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.SemifreeBasisEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # 底変更による semifree 性の保存

概要：可換環の任意の準同型に沿う底変更は semifree 複体を semifree 複体へ送る。
方針：各次数の基底を底変更し、微分の基底座標が元の座標の像であることを使う。
規約：平坦性は仮定しない。使われ方：導来 ∞ 圏の底変更関手の対象の閉性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {S T : Type u} [CommRing S] [CommRing T]

/-- 概要：環準同型に沿う複体の底変更関手。
方針：Mathlib の加群のスカラー拡大関手を各次数に適用する。
規約：微分は 1 ⊗ d。使われ方：底変更後の semifree 複体。 -/
abbrev complexBaseChange (f : S →+* T) : Complex S ⥤ Complex T :=
  (ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)

namespace ComplexSemifreeBasis
variable {P : Complex S} (B : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis S P) (f : S →+* T)

/-- 概要：底変更した複体の各次数の基底。
方針：元の基底を Mathlib の baseChange で移す。
規約：基底添字を変えない。使われ方：高さ関数の保持。 -/
def baseChangeBasis (k : ℤ) : Module.Basis (B.Index k) T
    (((complexBaseChange f).obj P).X k) := by
  letI := f.toAlgebra
  exact (B.basis k).baseChange T

/-- 概要：底変更後の基底の微分座標は元の微分座標を環準同型で写したものである。
方針：基底ベクトルが 1 ⊗ b であり、微分が 1 ⊗ d であることを展開する。
規約：環準同型は任意。使われ方：微分の台は増えないこと。 -/
theorem baseChangeBasis_d_repr (k : ℤ) (i : B.Index k) (j : B.Index (k + 1)) :
    (B.baseChangeBasis f (k + 1)).repr
      ((((complexBaseChange f).obj P).d k (k + 1)).hom (B.baseChangeBasis f k i)) j =
      f ((B.basis (k + 1)).repr ((P.d k (k + 1)).hom (B.basis k i)) j) := by
  letI := f.toAlgebra
  change ((B.basis (k + 1)).baseChange T).repr
    ((P.d k (k + 1)).hom.baseChange T ((B.basis k).baseChange T i)) j = _
  rw [Module.Basis.baseChange_apply, LinearMap.baseChange_tmul,
    Module.Basis.baseChange_repr_tmul]
  change f _ * 1 = _
  exact mul_one _

/-- 概要：任意の底変更は semibasis を保存する。
方針：高さを保持し、底変更後の非零座標から元の非零座標を得る。
規約：単射性・平坦性は不要。使われ方：既存定義での semifree 保存。 -/
def baseChange : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis T ((complexBaseChange f).obj P) where
  Index := B.Index
  basis := B.baseChangeBasis f
  height := B.height
  lowering k i j hj := by
    apply B.lowering k i j
    apply Finsupp.mem_support_iff.mpr
    intro hz
    have hne := Finsupp.mem_support_iff.mp hj
    exact hne ((B.baseChangeBasis_d_repr f k i j).trans (by rw [hz, map_zero]))

end ComplexSemifreeBasis

/-- 概要：任意の環準同型に沿う底変更は既存の semifree 性を保存する。
方針：filtration から基底を取り出し、底変更した基底から filtration を戻す。
規約：可換環以外の条件を加えない。使われ方：導来底変更の semifree モデル。 -/
theorem complexSemifree_baseChange (f : S →+* T) {P : Complex S}
    (hP : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S P) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree T ((complexBaseChange f).obj P) := by
  obtain ⟨B⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_nonempty_basis hP
  exact (B.baseChange f).complexSemifree

end SerrePositivity.InfinityCategories.Project.DerivedCategories
