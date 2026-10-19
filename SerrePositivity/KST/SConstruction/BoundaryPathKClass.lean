module
public import SerrePositivity.KST.SConstruction.BoundaryGroupoidSingleObject

/-! # 元の基本亜群の道を実際の零次 K 類へ戻す
概要：元の境界商の道を実際の加法記法の BF 零次群へ戻し、演算と対象類を照合する。
方針：既存の基本亜群表示の逆を用い、単位・合成・逆の式を移す。
規約：対象の辺は負の対象 K 類となる。使われ方：対象類による生成と K₀ 比較の全射性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra
open scoped Simplicial

/-- 元の境界商の基点の道を実際の加法記法の BF 零次 K 群へ戻す。 -/
def boundaryPathKClass (X : StableModel.{u})
    (f : boundaryFundamentalBasepoint X ⟶ boundaryFundamentalBasepoint X) :
    Additive (OmegaSpectrum.homotopyGroup (kOmegaSpectrum X) 0) :=
  Additive.ofMul ((kZeroGroupoidPresentation X).symm f)

/-- 元の恒等道の K 類は零。 -/
lemma boundaryPathKClass_id (X : StableModel.{u}) :
    boundaryPathKClass X (𝟙 (boundaryFundamentalBasepoint X)) = 0 := by
  apply Additive.toMul.injective
  apply (kZeroGroupoidPresentation X).injective
  change kZeroGroupoidPresentation X ((kZeroGroupoidPresentation X).symm (𝟙 _)) =
    kZeroGroupoidPresentation X 1
  rw [Equiv.apply_symm_apply, kZeroGroupoidPresentation_one]

/-- 元の道の合成は実際の K 類の和となる。 -/
lemma boundaryPathKClass_comp (X : StableModel.{u})
    (f g : boundaryFundamentalBasepoint X ⟶ boundaryFundamentalBasepoint X) :
    boundaryPathKClass X (f ≫ g) = boundaryPathKClass X f + boundaryPathKClass X g := by
  apply Additive.toMul.injective
  apply (kZeroGroupoidPresentation X).injective
  change kZeroGroupoidPresentation X ((kZeroGroupoidPresentation X).symm (f ≫ g)) =
    kZeroGroupoidPresentation X
      ((kZeroGroupoidPresentation X).symm f * (kZeroGroupoidPresentation X).symm g)
  rw [Equiv.apply_symm_apply, kZeroGroupoidPresentation_mul,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- 元の道の逆は実際の K 類の符号を反転する。 -/
lemma boundaryPathKClass_inv (X : StableModel.{u})
    (f : boundaryFundamentalBasepoint X ⟶ boundaryFundamentalBasepoint X) :
    boundaryPathKClass X (inv f) = -boundaryPathKClass X f := by
  apply Additive.toMul.injective
  apply (kZeroGroupoidPresentation X).injective
  change kZeroGroupoidPresentation X ((kZeroGroupoidPresentation X).symm (inv f)) =
    kZeroGroupoidPresentation X (((kZeroGroupoidPresentation X).symm f)⁻¹)
  rw [Equiv.apply_symm_apply, kZeroGroupoidPresentation_inv, Equiv.apply_symm_apply]

/-- 元の object S₁ の辺は、同じ評価対象の負の K 類に対応する。 -/
lemma boundaryPathKClass_object (X : StableModel.{u})
    (d : (objectSConstruction X.carrier) _⦋1⦌) :
    boundaryPathKClass X (objectBoundaryPath X d) =
      -objectKClass X ((sOneComparison X.carrier).app _ d) := by
  have h : -boundaryPathKClass X (objectBoundaryPath X d) =
      objectKClass X ((sOneComparison X.carrier).app _ d) := by
    rw [← boundaryPathKClass_inv]
    apply Additive.toMul.injective
    change (kZeroGroupoidPresentation X).symm (inv (objectBoundaryPath X d)) = _
    exact (kZeroGroupoidPresentation X).symm_apply_eq.mpr
      (kZeroGroupoidPresentation_objectKClass X d).symm
  exact neg_eq_iff_eq_neg.mp h

/-- 基本亜群表示の道を戻すと、元の実際の K 類を回収する。 -/
lemma boundaryPathKClass_presentation (X : StableModel.{u})
    (a : Additive (OmegaSpectrum.homotopyGroup (kOmegaSpectrum X) 0)) :
    boundaryPathKClass X (kZeroGroupoidPresentation X a.toMul) = a :=
  congrArg Additive.ofMul ((kZeroGroupoidPresentation X).symm_apply_apply a.toMul)

end SerrePositivity.KST.SConstruction
