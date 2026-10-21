module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedSectionEquivalence
public import SerrePositivity.InfinityCategories.Derived.DGUniversalRightAdjunction
public import SerrePositivity.InfinityCategories.Derived.DGKernelRightAdjointCandidate
/-!
概要：元の一般 kernel の実導来 ∞ 関手と同じ右随伴候補の随伴を構成する。
方針：厳密切断の全関手同値と、普遍余単位からの随伴を合成する。
規約：生の出力の射影性と大きい分解圏の Small 性は仮定しない。
使われ方：一般 RHom の実 ∞ 関手と三角恒等式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- 元の一般 kernel 作用と同じ実右随伴による、両三角式付き ∞ 随伴。 -/
def dgKernelAdjunction (P : Bimodule R E D) :
    QCatAdjunction (dgKernelDerivedInfinity R D E P) (dgKernelRightAdjointCandidate R D E P) := by
  let F := dgSemifreeKernelModuleDG R D E P
  let G := dgModuleFunctorResolutionReplacement R (SemifreeDGModules R D) E F
  let a := dgUniversalRightAdjunction R
    (DGModuleFunctorResolutionObject R (SemifreeDGModules R D) E F)
    (SemifreeDGModules R E) G (fun y => ⟨dgKernelResolutionUniversalCounit R D E P y⟩)
  let b := (dgModuleResolvedSourceSectionEquivalence R (SemifreeDGModules R D) E F).toAdjunction
  have q := b.comp a
  change QCatAdjunction (dgModuleResolvedInfinity R (SemifreeDGModules R D) E F) _
  rw [dgModuleResolvedInfinity_eq_section_replacement]
  exact q
end SerrePositivity.InfinityCategories
