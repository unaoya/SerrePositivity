module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.BaseComparisonExt
public import SerrePositivity.AlgebraicGeometry.BlowupFunctor
public import SerrePositivity.AlgebraicGeometry.PowerBlowup

/-!
概要：KST §5 の冪による blowup 同型の係数環写像に関する自然性。
方針：両方の比較が基底上の射であることを確認し、分離性による一意性を適用する。
規約：中心を保つ環準同型は任意、冪指数は正。
使われ方：冪不変性の同型を一般スキーム上へ貼り合わせる。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
variable {R S : Type u} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)

set_option backward.isDefEq.respectTransparency false in
/--
概要：正の冪による blowup の同型は中心を保つ係数環写像と両立する。
方針：基底上の二つの合成を、像中心の blowup からの射の一意性で比較する。
規約：KST §5、有限生成性・平坦性は不要。
使われ方：アフィン開集合の包含に関する冪比較同型の自然性。
-/
@[reassoc] theorem affineBlowupPowerIso_naturality (f : R →+* S) (hJ : I.map f = J)
    (n : ℕ) (hn : 0 < n) :
    affineBlowupCenterMap (I ^ n) (J ^ n) f (by rw [Ideal.map_pow, hJ]) ≫
        (affineBlowupPowerIso I n hn).hom =
      (affineBlowupPowerIso J n hn).hom ≫ affineBlowupCenterMap I J f hJ := by
  apply affineBlowupCenter_hom_ext (I ^ n) f (J ^ n) (by rw [Ideal.map_pow, hJ])
    (affineBlowupπ I)
  · intro a
    exact affineBlowupπ_restrict_basicOpen_isIso I ⟨a.1, I.pow_le_self hn.ne' a.2⟩
  · simp only [Category.assoc, affineBlowupPowerIso_hom_base, affineBlowupCenterMap_base]
  · simp only [Category.assoc, affineBlowupCenterMap_base, affineBlowupPowerIso_hom_base_assoc]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
