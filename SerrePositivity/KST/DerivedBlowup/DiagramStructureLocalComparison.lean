module

public import SerrePositivity.KST.DerivedBlowup.DiagramStructureModule
public import SerrePositivity.KST.DerivedBlowup.RawRestrictionCoherence
public import SerrePositivity.KST.DerivedBlowup.DiagramRepresentableLocalPerfect
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraDerivedEvaluation
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraLocallyPerfect

/-!
概要：KST §3.1 の構造図式加群の局所 regular 比較と局所 perfect 性。
方針：元の局所埋め込みと補助始点つき係数圏の埋め込みを比較し、代表加群の局所計算を使う。
規約：大域係数圏の既存 small 仮定を保ち、補助係数圏の small 仮定を追加しない。
使われ方：構造加群の cartesian perfect 性と生成系の構成。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory Opposite
open DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable (F : J ⥤ Mon (Complex R))

/-- 概要：元の局所頂点の埋め込みは補助始点つき係数圏の局所埋め込みと整合する。
方針：対象は元の頂点、Hom は包含同定の合成として比較する。
規約：KST §3.1。使われ方：構造加群の反復制限と直接局所制限の比較。 -/
theorem diagramAlgebraBottomInclusion_vertex (i : J) :
    (diagramAlgebraVertexEmbedding F i).comp (diagramAlgebraBottomInclusion F) =
      diagramAlgebraVertexEmbedding (diagramAlgebraWithBottom F) (i : WithBot J) := by
  refine EnrichedFunctor.ext (Complex R) (fun _ => rfl) ?_
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  change diagramModuleHomInclusion F (le_refl i) ≫
      eqToHom (diagramAlgebraWithBottom_hom F i i) =
    diagramModuleHomInclusion (diagramAlgebraWithBottom F) (le_refl (i : WithBot J))
  simp only [diagramModuleHomInclusion, eqToHom_trans]

variable [Small.{u} (DiagramModuleCoefficientObject F)]

/-- 概要：構造図式加群の局所評価は補助 representable の直接局所制限と同型。
方針：埋め込みの整合性に raw 加群の制限合成同型を適用する。
規約：KST §3.1。使われ方：局所 perfect 性の計算を実際の構造加群へ移す。 -/
def diagramStructureLocalComparisonIso (i : J) :
    (diagramAlgebraModuleEvaluation F i).obj (diagramStructureModule F) ≅
      ForgetEnrichment.of (Complex R)
        (diagramRepresentableLocalRaw (diagramAlgebraWithBottom F) ⊥ (i : WithBot J)) :=
  rawTransitionRestrictionCompIso R (diagramAlgebraVertexEmbedding F i)
    (diagramAlgebraBottomInclusion F)
    (diagramAlgebraVertexEmbedding (diagramAlgebraWithBottom F) (i : WithBot J))
    (diagramAlgebraBottomInclusion_vertex F i)
    (representable R (op (⟨⊥⟩ : DiagramModuleCoefficientObject (diagramAlgebraWithBottom F))))

/-- 概要：構造図式加群の局所導来評価は局所 regular 代表加群の主導来像と同型。
方針：補助 representable の指定 regular 擬同型と制限合成比較を接続する。
規約：KST §3.1。使われ方：構造加群の局所自由性と perfect 性。 -/
def diagramStructureLocalRegularDerivedIso (i : J) :
    (moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).obj
      (ForgetEnrichment.of (Complex R) (representable R (op (.point : AlgebraVertex (F.obj i))))) ≅
      (diagramAlgebraDerivedEvaluation F i).obj (derivedDiagramStructureModule F) :=
  diagramRepresentableLocalRegularDerivedIso (diagramAlgebraWithBottom F)
      (bot_le : (⊥ : WithBot J) ≤ (i : WithBot J)) ≪≫
    ((moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).mapIso
      (diagramStructureLocalComparisonIso F i)).symm

/-- 概要：構成済み構造図式加群は全頂点で局所 perfect。
方針：各頂点の指定 regular 導来同型に沿って代表生成元の perfect 性を移す。
規約：KST §3.1、cartesian 条件の証明は別に残す。
使われ方：大域構造加群の Perf 候補への所属。 -/
theorem diagramStructureModule_locallyPerfect :
    diagramAlgebraLocallyPerfect F (derivedDiagramStructureModule F) := by
  intro i
  exact (modulePerfect R (AlgebraVertex (F.obj i))ᵒᵖ).prop_of_iso
    (diagramStructureLocalRegularDerivedIso F i)
    (modulePerfectOver_representable R (AlgebraVertex (F.obj i))ᵒᵖ
      (op .point) (Set.mem_univ _))

end SerrePositivity.KST.DerivedBlowup
