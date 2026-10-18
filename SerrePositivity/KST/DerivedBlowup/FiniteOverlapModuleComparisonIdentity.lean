module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapModuleRestrictionCoherence

/-!
概要：KST §3.1 の指定局所加群比較の単位条件。
方針：加群射を underlying 複体で評価し、指定単位矢作用の関手性へ戻す。
規約：行先は固定した局所制限の標準合成同型で揃える。
使われ方：導来局所比較の coherent な包含鎖への接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory Opposite
open DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：恒等包含の指定局所加群比較は標準制限単位同型を介して恒等。
方針：各成分で指定単位矢作用の恒等律へ戻す。
規約：KST §3.1。使われ方：導来局所比較の単位条件の入力。 -/
theorem finiteOverlapModuleComparison_id (a : I → R) (T : FiniteOverlapIndex I)
    (M : AllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    finiteOverlapModuleComparison R a (le_refl T) M ≫
      (finiteOverlapLocalModuleRestrictionIdIso R a T).hom.app
        ((finiteOverlapModuleEvaluation R a T).obj M) = 𝟙 _ := by
  apply moduleMorphism_ext
  intro x
  have hx : x = op .point := by
    apply Opposite.unop_injective
    cases x.unop
    rfl
  subst x
  rw [Functor.map_comp, CategoryTheory.Functor.map_id, finiteOverlapModuleComparison_eval,
    finiteOverlapLocalModuleRestrictionIdIso_hom_eval]
  change (diagramModuleUnderlyingDiagram (finiteOverlapDGAlgebraDiagram R a)
    (ForgetEnrichment.to (Complex R) M)).map (homOfLE (le_refl T)) ≫ 𝟙 _ = 𝟙 _
  simpa only [Category.comp_id] using diagramModuleUnderlyingDiagram_id _
    (ForgetEnrichment.to (Complex R) M) T

end SerrePositivity.KST.DerivedBlowup
