module

public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraDerivedExtensionAssociativity

/-!
概要：KST §3.1 の標準局所導来係数拡大同型の左右の単位整合性。
方針：共役対応の単射性と単位子・whisker の公式を使う。
規約：標準制限同型の逆の単位条件へ移す。
使われ方：局所係数拡大の擬関手の単位条件。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.Functor
open DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J]
variable (F : J ⥤ Mon (Complex R))

set_option maxHeartbeats 2000000 in
-- 恒等随伴を含む合成 graph 随伴と共役対応を照合するために必要。
/-- 概要：始点の恒等包含との標準係数拡大合成同型は始点の単位同型に一致する。
方針：共役像を計算し、標準制限同型の逆の左単位条件を使う。
規約：KST §3.1。使われ方：標準係数拡大の左単位条件。 -/
theorem diagramAlgebraDerivedExtensionCompIso_left_unit {i j : J} (h : i ≤ j) :
    (diagramAlgebraDerivedExtensionCompIso F (le_refl i) h).hom =
      whiskerRight (diagramAlgebraDerivedExtensionIdIso F i).hom
        (diagramAlgebraDerivedExtension F h) ≫
        (leftUnitor (diagramAlgebraDerivedExtension F h)).hom := by
  apply (conjugateEquiv (diagramAlgebraDerivedAdjunction F h)
    ((diagramAlgebraDerivedAdjunction F (le_refl i)).comp
      (diagramAlgebraDerivedAdjunction F h))).injective
  rw [diagramAlgebraDerivedExtensionCompIso_conjugate,
    diagramAlgebraDerivedRestrictionCompIso_inv_left_unit]
  symm
  rw [← conjugateEquiv_comp (diagramAlgebraDerivedAdjunction F h)
    (Adjunction.id.comp (diagramAlgebraDerivedAdjunction F h))]
  rw [conjugateEquiv_leftUnitor_hom, conjugateEquiv_whiskerRight,
    diagramAlgebraDerivedExtensionIdIso_conjugate]
  have hu : (rightUnitor (diagramAlgebraDerivedRestriction F h)).inv = 𝟙 _ := by
    ext X
    rfl
  rw [hu, Category.id_comp]

set_option maxHeartbeats 2000000 in
-- 恒等随伴を含む合成 graph 随伴と共役対応を照合するために必要。
/-- 概要：終点の恒等包含との標準係数拡大合成同型は終点の単位同型に一致する。
方針：共役像を計算し、標準制限同型の逆の右単位条件を使う。
規約：KST §3.1。使われ方：標準係数拡大の右単位条件。 -/
theorem diagramAlgebraDerivedExtensionCompIso_right_unit {i j : J} (h : i ≤ j) :
    (diagramAlgebraDerivedExtensionCompIso F h (le_refl j)).hom =
      whiskerLeft (diagramAlgebraDerivedExtension F h)
        (diagramAlgebraDerivedExtensionIdIso F j).hom ≫
        (rightUnitor (diagramAlgebraDerivedExtension F h)).hom := by
  apply (conjugateEquiv (diagramAlgebraDerivedAdjunction F h)
    ((diagramAlgebraDerivedAdjunction F h).comp
      (diagramAlgebraDerivedAdjunction F (le_refl j)))).injective
  rw [diagramAlgebraDerivedExtensionCompIso_conjugate,
    diagramAlgebraDerivedRestrictionCompIso_inv_right_unit]
  symm
  rw [← conjugateEquiv_comp (diagramAlgebraDerivedAdjunction F h)
    ((diagramAlgebraDerivedAdjunction F h).comp Adjunction.id)]
  rw [conjugateEquiv_rightUnitor_hom, conjugateEquiv_whiskerLeft,
    diagramAlgebraDerivedExtensionIdIso_conjugate]
  have hu : (leftUnitor (diagramAlgebraDerivedRestriction F h)).inv = 𝟙 _ := by
    ext X
    rfl
  rw [hu, Category.id_comp]

end SerrePositivity.KST.DerivedBlowup
