module

public import SerrePositivity.KST.DerivedBlowup.AdjointComparisonConjugate
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraDerivedExtensionCoherence
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraDerivedRestrictionUnits

/-!
概要：KST §3.1 の標準導来係数拡大同型と標準制限同型の共役対応。
方針：指定左随伴比較と共役対応の一般公式を graph 随伴へ適用する。
規約：標準係数拡大同型の共役像は標準制限同型の逆。
使われ方：標準係数拡大同型の結合・単位整合性。
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

/-- 概要：正規表示の局所遷移に沿う指定導来延長–制限随伴。
方針：構成済み graph tensor の導来随伴を使う。
規約：KST §3.1。使われ方：共役対応の随伴引数。 -/
abbrev diagramAlgebraDerivedAdjunction {i j : J} (h : i ≤ j) :=
  dgDerivedExtensionRestrictionAdjunction R (AlgebraVertex (F.obj i))ᵒᵖ
    (AlgebraVertex (F.obj j))ᵒᵖ (diagramAlgebraVertexTransition F h).op

/-- 概要：標準導来係数拡大単位同型の共役像は標準制限単位同型の逆。
方針：左随伴一意性と共役対応の一般比較を恒等随伴に適用する。
規約：KST §3.1。使われ方：標準係数拡大の単位条件。 -/
theorem diagramAlgebraDerivedExtensionIdIso_conjugate (i : J) :
    conjugateEquiv (Adjunction.id (C := DerivedModuleCategory R (AlgebraVertex (F.obj i))ᵒᵖ))
      (diagramAlgebraDerivedAdjunction F (le_refl i))
      (diagramAlgebraDerivedExtensionIdIso F i).hom =
        (diagramAlgebraDerivedRestrictionIdIso F i).inv :=
  adjointComparison_conjugate (diagramAlgebraDerivedAdjunction F (le_refl i))
    Adjunction.id (diagramAlgebraDerivedRestrictionIdIso F i)

/-- 概要：標準導来係数拡大合成同型の共役像は標準制限合成同型の逆。
方針：左随伴一意性と共役対応の一般比較を合成 graph 随伴に適用する。
規約：KST §3.1。使われ方：標準係数拡大の結合条件。 -/
theorem diagramAlgebraDerivedExtensionCompIso_conjugate {i j k : J}
    (h : i ≤ j) (g : j ≤ k) :
    conjugateEquiv (diagramAlgebraDerivedAdjunction F (h.trans g))
      ((diagramAlgebraDerivedAdjunction F h).comp (diagramAlgebraDerivedAdjunction F g))
      (diagramAlgebraDerivedExtensionCompIso F h g).hom =
        (diagramAlgebraDerivedRestrictionCompIso F h g).inv :=
  adjointComparison_conjugate
    ((diagramAlgebraDerivedAdjunction F h).comp (diagramAlgebraDerivedAdjunction F g))
    (diagramAlgebraDerivedAdjunction F (h.trans g))
    (diagramAlgebraDerivedRestrictionCompIso F h g)

end SerrePositivity.KST.DerivedBlowup
