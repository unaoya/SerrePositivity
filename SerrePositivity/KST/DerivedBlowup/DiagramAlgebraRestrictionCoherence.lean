module

public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraVertex
public import SerrePositivity.KST.DerivedBlowup.TransitionRestrictionCoherence

/-!
概要：KST §3.1 の一対象正規表示での局所加群制限の標準単位・合成同型。
方針：正規表示の恒等・合成律を一般の制限比較へ適用する。
規約：対象写像が標準点に固定されるため評価成分は任意の局所加群上で恒等。
使われ方：指定局所加群比較の単位・三重整合性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory Opposite
open DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J]
variable (F : J ⥤ Mon (Complex R))

/-- 概要：正規表示の恒等局所制限から恒等関手への標準同型。
方針：局所遷移の恒等律と一般の制限単位比較を使う。
規約：KST §3.1。使われ方：指定加群比較の単位条件。 -/
abbrev diagramAlgebraRestrictionIdIso (i : J) :=
  transitionRestrictionIdIso (diagramAlgebraVertexTransition F (le_refl i))
    (diagramAlgebraVertexTransition_id F i)

/-- 概要：正規表示の二段の局所制限から直接制限への標準同型。
方針：局所遷移の合成律と一般の制限合成比較を使う。
規約：KST §3.1。使われ方：三重加群比較の行先の同定。 -/
abbrev diagramAlgebraRestrictionCompIso {i j k : J} (h : i ≤ j) (g : j ≤ k) :=
  transitionRestrictionCompIso (diagramAlgebraVertexTransition F h)
    (diagramAlgebraVertexTransition F g) (diagramAlgebraVertexTransition F (h.trans g))
    (diagramAlgebraVertexTransition_comp F h g)

/-- 概要：正規表示の局所制限単位同型の標準点での評価は恒等。
方針：一般評価の対象移送を、標準点に固定した対象写像で簡約する。
規約：KST §3.1。使われ方：指定加群比較の単位条件の評価。 -/
theorem diagramAlgebraRestrictionIdIso_hom_eval (i : J)
    (M : ModuleCategory R (AlgebraVertex (F.obj i))ᵒᵖ) :
    (moduleEvaluation R (AlgebraVertex (F.obj i))ᵒᵖ (op .point)).map
      ((diagramAlgebraRestrictionIdIso F i).hom.app M) = 𝟙 _ :=
  transitionRestrictionIdIso_eval (diagramAlgebraVertexTransition F (le_refl i))
    (diagramAlgebraVertexTransition_id F i) M .point

/-- 概要：正規表示の局所制限合成同型の標準点での評価は恒等。
方針：一般評価の対象移送を、標準点に固定した対象写像で簡約する。
規約：KST §3.1、全図式からの制限加群だけでなく任意の局所加群で成り立つ。
使われ方：指定加群比較の三重条件の評価。 -/
theorem diagramAlgebraRestrictionCompIso_hom_eval {i j k : J} (h : i ≤ j) (g : j ≤ k)
    (M : ModuleCategory R (AlgebraVertex (F.obj k))ᵒᵖ) :
    (moduleEvaluation R (AlgebraVertex (F.obj i))ᵒᵖ (op .point)).map
      ((diagramAlgebraRestrictionCompIso F h g).hom.app M) = 𝟙 _ :=
  transitionRestrictionCompIso_eval (diagramAlgebraVertexTransition F h)
    (diagramAlgebraVertexTransition F g) (diagramAlgebraVertexTransition F (h.trans g))
    (diagramAlgebraVertexTransition_comp F h g) M .point

end SerrePositivity.KST.DerivedBlowup
