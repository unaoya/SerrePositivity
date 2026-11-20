module

public import SerrePositivity.AlgebraicGeometry.ProductBlowup
public import SerrePositivity.AlgebraicGeometry.BaseComparisonExt
public import SerrePositivity.AlgebraicGeometry.BlowupFunctor

/-!
概要：KST §5、Stacks 080Y の積中心の比較射の係数環写像に対する自然性。
方針：積中心の blowup からの基底上の射の一意性を使う。
規約：中心を保つ係数写像は任意、平坦性や有限生成性を仮定しない。
使われ方：二つの blowup の共通細分を一般スキーム上へ貼り合わせる。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
variable {R S : Type u} [CommRing R] [CommRing S]
  (I J : Ideal R) (I' J' : Ideal S)

set_option backward.isDefEq.respectTransparency false in
/--
概要：積中心から第一の中心への blowup 比較射は係数環の写像と両立する。
方針：積中心の各元は第一の中心に属するので、分離性による一意性を適用する。
規約：KST §5、Stacks 080Y、二つの像中心の等式を明示する。
使われ方：アフィン開集合の包含に関する比較射の自然性。
-/
@[reassoc] theorem affineBlowupProductLeftMap_naturality (f : R →+* S)
    (hI : I.map f = I') (hJ : J.map f = J') :
    affineBlowupCenterMap (I * J) (I' * J') f (by rw [Ideal.map_mul, hI, hJ]) ≫
        affineBlowupProductLeftMap I J =
      affineBlowupProductLeftMap I' J' ≫ affineBlowupCenterMap I I' f hI := by
  apply affineBlowupCenter_hom_ext (I * J) f (I' * J')
    (by rw [Ideal.map_mul, hI, hJ]) (affineBlowupπ I)
  · intro a
    exact affineBlowupπ_restrict_basicOpen_isIso I ⟨a.1, Ideal.mul_le_left a.2⟩
  · simp only [Category.assoc, affineBlowupProductLeftMap_base, affineBlowupCenterMap_base]
  · simp only [Category.assoc, affineBlowupCenterMap_base, affineBlowupProductLeftMap_base_assoc]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
