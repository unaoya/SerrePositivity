module
public import SerrePositivity.InfinityCategories.Derived.DGUniversalCommaCounit
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedSectionIso
public import SerrePositivity.InfinityCategories.Derived.DGKernelRightAdjointCandidate
/-!
概要：実入力切断の同じ比較を通じ、一般 kernel の右随伴候補に実余単位を戻す。
方針：入力射影と指定切断の全関手同型を、普遍余単位の全関手ホモトピーへ合成する。
規約：随伴の三角式は別工程。使われ方：元の一般 kernel ∞ 作用の ∞ 随伴判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- 元の右随伴候補との合成を、同じ普遍余単位の合成へ比較する。 -/
def dgKernelRightAdjointCompositeIso (P : Bimodule R E D) :
    FunctorIso (dgKernelRightAdjointCandidate R D E P ≫ dgKernelDerivedInfinity R D E P)
      (dgUniversalRightAdjointCandidate R
        (DGModuleFunctorResolutionObject R (SemifreeDGModules R D) E
          (dgSemifreeKernelModuleDG R D E P)) (SemifreeDGModules R E)
        (dgModuleFunctorResolutionReplacement R (SemifreeDGModules R D) E
          (dgSemifreeKernelModuleDG R D E P))
        (fun y => ⟨dgKernelResolutionUniversalCounit R D E P y⟩) ≫
          dgNerve.map (dgModuleFunctorResolutionReplacement R (SemifreeDGModules R D) E
            (dgSemifreeKernelModuleDG R D E P))) := by
  let C := SemifreeDGModules R D
  let F := dgSemifreeKernelModuleDG R D E P
  let T := DGModuleFunctorResolutionObject R C E F
  let G := dgModuleFunctorResolutionReplacement R C E F
  let R' := dgUniversalRightAdjointCandidate R T (SemifreeDGModules R E) G
    (fun y => ⟨dgKernelResolutionUniversalCounit R D E P y⟩)
  have e := ((dgModuleResolvedProjectionSectionIso R C E F).postcomp
    (dgNerve.map G)).precomp R'
  change FunctorIso ((R' ≫ dgNerve.map (dgModuleFunctorResolutionSource R C E F)) ≫
    dgModuleResolvedInfinity R C E F) (R' ≫ dgNerve.map G)
  rw [dgModuleResolvedInfinity_eq_section_replacement]
  simpa only [Category.assoc, Category.id_comp] using! e
/-- 元の kernel 作用の右随伴候補の、同じ実比較から得る h Fun の余単位。 -/
def dgKernelCounitCandidate (P : Bimodule R E D) :
    FunctorHom (dgKernelRightAdjointCandidate R D E P ≫ dgKernelDerivedInfinity R D E P)
      (𝟙 _) :=
  (dgKernelRightAdjointCompositeIso R D E P).hom ≫
    dgUniversalRightAdjointCounit R
      (DGModuleFunctorResolutionObject R (SemifreeDGModules R D) E
        (dgSemifreeKernelModuleDG R D E P)) (SemifreeDGModules R E)
      (dgModuleFunctorResolutionReplacement R (SemifreeDGModules R D) E
        (dgSemifreeKernelModuleDG R D E P))
      (fun y => ⟨dgKernelResolutionUniversalCounit R D E P y⟩)
/-- 同じ余単位の類を保つ、全関手ホモトピーの実代表。 -/
def dgKernelCounitCandidateHomotopy (P : Bimodule R E D) :
    SSet.Homotopy
      (dgKernelRightAdjointCandidate R D E P ≫ dgKernelDerivedInfinity R D E P) (𝟙 _) :=
  functorHomHomotopy (dgKernelCounitCandidate R D E P)
/-- 選んだ実ホモトピーは、元の同じ全関手の余単位を回収する。 -/
lemma dgKernelCounitCandidateHomotopy_hom (P : Bimodule R E D) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (dgKernelCounitCandidateHomotopy R D E P)) = dgKernelCounitCandidate R D E P :=
  functorHomHomotopy_hom _
end SerrePositivity.InfinityCategories
