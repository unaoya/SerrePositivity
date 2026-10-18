module

public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraRestrictionCoherence
public import SerrePositivity.KST.DerivedBlowup.TransitionDerivedRestrictionComputation

/-!
概要：KST §3.1 の一対象正規表示での導来制限単位・合成同型。
方針：正規表示の局所遷移の等式を一般の標準導来比較へ適用する。
規約：実加群の局所化像上で元の制限同型の局所化像と一致する。
使われ方：指定導来制限比較の単位・三重条件の行先を同定する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J]
variable (F : J ⥤ Mon (Complex R))

/-- 概要：正規表示の恒等局所導来制限から恒等関手への標準同型。
方針：局所 dg 恒等律と一般の導来制限単位同型を使う。
規約：KST §3.1。使われ方：指定導来比較の単位条件。 -/
abbrev diagramAlgebraDerivedRestrictionIdIso (i : J) :=
  transitionDerivedRestrictionIdIso (diagramAlgebraVertexTransition F (le_refl i))
    (diagramAlgebraVertexTransition_id F i)

/-- 概要：正規表示の二段の局所導来制限から直接制限への標準同型。
方針：局所 dg 合成律と一般の導来制限合成同型を使う。
規約：KST §3.1。使われ方：指定導来比較の三重条件の行先。 -/
abbrev diagramAlgebraDerivedRestrictionCompIso {i j k : J} (h : i ≤ j) (g : j ≤ k) :=
  transitionDerivedRestrictionCompIso (diagramAlgebraVertexTransition F h)
    (diagramAlgebraVertexTransition F g) (diagramAlgebraVertexTransition F (h.trans g))
    (diagramAlgebraVertexTransition_comp F h g)

/-- 概要：標準導来制限単位同型の実加群上の順成分。
方針：一般の計算公式を正規表示へ適用する。
規約：KST §3.1。使われ方：単位条件を局所化前へ戻す。 -/
theorem diagramAlgebraDerivedRestrictionIdIso_hom_app_Q (i : J)
    (M : ModuleCategory R (AlgebraVertex (F.obj i))ᵒᵖ) :
    (diagramAlgebraDerivedRestrictionIdIso F i).hom.app
        ((moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).obj M) =
      (moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).map
        ((diagramAlgebraRestrictionIdIso F i).hom.app M) :=
  transitionDerivedRestrictionIdIso_hom_app_Q (diagramAlgebraVertexTransition F (le_refl i))
    (diagramAlgebraVertexTransition_id F i) M

/-- 概要：標準導来制限合成同型の実加群上の順成分。
方針：一般の計算公式を正規表示へ適用する。
規約：KST §3.1。使われ方：三重条件を局所化前へ戻す。 -/
theorem diagramAlgebraDerivedRestrictionCompIso_hom_app_Q {i j k : J} (h : i ≤ j) (g : j ≤ k)
    (M : ModuleCategory R (AlgebraVertex (F.obj k))ᵒᵖ) :
    (diagramAlgebraDerivedRestrictionCompIso F h g).hom.app
        ((moduleToDerived R (AlgebraVertex (F.obj k))ᵒᵖ).obj M) =
      (moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).map
        ((diagramAlgebraRestrictionCompIso F h g).hom.app M) :=
  transitionDerivedRestrictionCompIso_hom_app_Q (diagramAlgebraVertexTransition F h)
    (diagramAlgebraVertexTransition F g) (diagramAlgebraVertexTransition F (h.trans g))
    (diagramAlgebraVertexTransition_comp F h g) M

end SerrePositivity.KST.DerivedBlowup
