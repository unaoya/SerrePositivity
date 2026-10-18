module

public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraDerivedExtensionConjugate
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraDerivedRestrictionInverseCoherence

/-!
概要：KST §3.1 の標準局所導来係数拡大同型の結合整合性。
方針：共役対応の単射性で標準制限同型の逆の四頂点整合性へ戻す。
規約：関手の結合子を明示して二つの指定合成経路を比較する。
使われ方：局所係数拡大の coherent な図式。
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

set_option maxHeartbeats 4000000 in
-- 四頂点の三つの合成随伴と共役対応を照合するために必要。
/-- 概要：標準導来係数拡大合成同型は四頂点の結合整合性を満たす。
方針：合成・whisker・結合子の共役公式を使い制限側の逆の結合条件へ送る。
規約：KST §3.1。使われ方：標準局所係数拡大の擬関手の合成条件。 -/
theorem diagramAlgebraDerivedExtensionCompIso_assoc {i j k l : J}
    (h : i ≤ j) (g : j ≤ k) (t : k ≤ l) :
    whiskerRight (diagramAlgebraDerivedExtensionCompIso F h g).hom
        (diagramAlgebraDerivedExtension F t) ≫
        (diagramAlgebraDerivedExtensionCompIso F (h.trans g) t).hom =
      (associator (diagramAlgebraDerivedExtension F h) (diagramAlgebraDerivedExtension F g)
          (diagramAlgebraDerivedExtension F t)).hom ≫
        whiskerLeft (diagramAlgebraDerivedExtension F h)
          (diagramAlgebraDerivedExtensionCompIso F g t).hom ≫
        (diagramAlgebraDerivedExtensionCompIso F h (g.trans t)).hom := by
  apply (conjugateEquiv (diagramAlgebraDerivedAdjunction F ((h.trans g).trans t))
    (((diagramAlgebraDerivedAdjunction F h).comp (diagramAlgebraDerivedAdjunction F g)).comp
      (diagramAlgebraDerivedAdjunction F t))).injective
  calc
    _ = (diagramAlgebraDerivedRestrictionCompIso F (h.trans g) t).inv ≫
        whiskerLeft (diagramAlgebraDerivedRestriction F t)
          (diagramAlgebraDerivedRestrictionCompIso F h g).inv := by
      rw [← conjugateEquiv_comp (diagramAlgebraDerivedAdjunction F ((h.trans g).trans t))
        ((diagramAlgebraDerivedAdjunction F (h.trans g)).comp
          (diagramAlgebraDerivedAdjunction F t))]
      rw [diagramAlgebraDerivedExtensionCompIso_conjugate, conjugateEquiv_whiskerRight,
        diagramAlgebraDerivedExtensionCompIso_conjugate]
    _ = (diagramAlgebraDerivedRestrictionCompIso F h (g.trans t)).inv ≫
        whiskerRight (diagramAlgebraDerivedRestrictionCompIso F g t).inv
          (diagramAlgebraDerivedRestriction F h) :=
      diagramAlgebraDerivedRestrictionCompIso_inv_assoc F h g t
    _ = _ := by
      symm
      rw [← conjugateEquiv_comp (diagramAlgebraDerivedAdjunction F ((h.trans g).trans t))
        ((diagramAlgebraDerivedAdjunction F h).comp
          ((diagramAlgebraDerivedAdjunction F g).comp (diagramAlgebraDerivedAdjunction F t)))]
      rw [← conjugateEquiv_comp (diagramAlgebraDerivedAdjunction F ((h.trans g).trans t))
        ((diagramAlgebraDerivedAdjunction F h).comp
          (diagramAlgebraDerivedAdjunction F (g.trans t)))]
      rw [diagramAlgebraDerivedExtensionCompIso_conjugate F h (g.trans t),
        conjugateEquiv_whiskerLeft
          (diagramAlgebraDerivedAdjunction F (g.trans t))
          ((diagramAlgebraDerivedAdjunction F g).comp (diagramAlgebraDerivedAdjunction F t))
          (diagramAlgebraDerivedAdjunction F h)
          (diagramAlgebraDerivedExtensionCompIso F g t).hom,
        diagramAlgebraDerivedExtensionCompIso_conjugate F g t,
        conjugateEquiv_associator_hom (diagramAlgebraDerivedAdjunction F h)
          (diagramAlgebraDerivedAdjunction F g) (diagramAlgebraDerivedAdjunction F t)]
      have ha : (associator (diagramAlgebraDerivedRestriction F t)
          (diagramAlgebraDerivedRestriction F g) (diagramAlgebraDerivedRestriction F h)).hom =
          𝟙 _ := by
        ext X
        rfl
      rw [ha, Category.comp_id]

end SerrePositivity.KST.DerivedBlowup
