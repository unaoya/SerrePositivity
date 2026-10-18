module

public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraDerivedRestrictionUnits

/-!
概要：KST §3.1 の標準導来制限同型の逆の整合性。
方針：順方向の自然変換等式を自然同型の等号にし、逆射を取る。
規約：共役対応で係数拡大側へ移す向きに等式を固定する。
使われ方：標準導来係数拡大同型の結合・単位条件。
-/

@[expose] public noncomputable section

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.Functor
open DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J]
variable (F : J ⥤ Mon (Complex R))

/-- 概要：標準導来制限同型の逆は四頂点の結合整合性を満たす。
方針：順方向の合成自然同型の等号から逆射の等号を取る。
規約：KST §3.1。使われ方：共役対応での結合条件。 -/
theorem diagramAlgebraDerivedRestrictionCompIso_inv_assoc {i j k l : J}
    (h : i ≤ j) (g : j ≤ k) (t : k ≤ l) :
    (diagramAlgebraDerivedRestrictionCompIso F (h.trans g) t).inv ≫
        whiskerLeft (diagramAlgebraDerivedRestriction F t)
          (diagramAlgebraDerivedRestrictionCompIso F h g).inv =
      (diagramAlgebraDerivedRestrictionCompIso F h (g.trans t)).inv ≫
        whiskerRight (diagramAlgebraDerivedRestrictionCompIso F g t).inv
          (diagramAlgebraDerivedRestriction F h) := by
  have he :
      isoWhiskerLeft (diagramAlgebraDerivedRestriction F t)
          (diagramAlgebraDerivedRestrictionCompIso F h g) ≪≫
        diagramAlgebraDerivedRestrictionCompIso F (h.trans g) t =
      isoWhiskerRight (diagramAlgebraDerivedRestrictionCompIso F g t)
          (diagramAlgebraDerivedRestriction F h) ≪≫
        diagramAlgebraDerivedRestrictionCompIso F h (g.trans t) :=
    Iso.ext (diagramAlgebraDerivedRestrictionCompIso_assoc F h g t)
  exact congrArg Iso.inv he

/-- 概要：始点の恒等包含との標準導来制限合成同型の逆は単位同型の逆に一致する。
方針：順方向の自然同型の等号から逆射を取る。
規約：KST §3.1。使われ方：共役対応での左単位条件。 -/
theorem diagramAlgebraDerivedRestrictionCompIso_inv_left_unit {i j : J} (h : i ≤ j) :
    (diagramAlgebraDerivedRestrictionCompIso F (le_refl i) h).inv =
      whiskerLeft (diagramAlgebraDerivedRestriction F h)
        (diagramAlgebraDerivedRestrictionIdIso F i).inv := by
  have he : diagramAlgebraDerivedRestrictionCompIso F (le_refl i) h =
      isoWhiskerLeft (diagramAlgebraDerivedRestriction F h)
        (diagramAlgebraDerivedRestrictionIdIso F i) :=
    Iso.ext (diagramAlgebraDerivedRestrictionCompIso_left_unit F h)
  exact congrArg Iso.inv he

/-- 概要：終点の恒等包含との標準導来制限合成同型の逆は単位同型の逆の制限に一致する。
方針：順方向の自然同型の等号から逆射を取る。
規約：KST §3.1。使われ方：共役対応での右単位条件。 -/
theorem diagramAlgebraDerivedRestrictionCompIso_inv_right_unit {i j : J} (h : i ≤ j) :
    (diagramAlgebraDerivedRestrictionCompIso F h (le_refl j)).inv =
      whiskerRight (diagramAlgebraDerivedRestrictionIdIso F j).inv
        (diagramAlgebraDerivedRestriction F h) := by
  have he : diagramAlgebraDerivedRestrictionCompIso F h (le_refl j) =
      isoWhiskerRight (diagramAlgebraDerivedRestrictionIdIso F j)
        (diagramAlgebraDerivedRestriction F h) :=
    Iso.ext (diagramAlgebraDerivedRestrictionCompIso_right_unit F h)
  exact congrArg Iso.inv he

end SerrePositivity.KST.DerivedBlowup
