module

public import SerrePositivity.KST.DerivedBlowup.DiagramGaugeFunctor
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraVertex
public import SerrePositivity.KST.DerivedBlowup.RawRestrictionCoherence

/-!
概要：KST §3.1 の Hom 重み付けは局所頂点への制限を保つ。
方針：対角の重みが恒等であることから局所埋め込みとの厳密な整合性を示す。
規約：大域の遷移は重みを持つが、局所の代数作用は元のままである。
使われ方：大域 O(m) の局所 regular 同型と局所 perfect 性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory Opposite DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable (F : J ⥤ Mon (Complex R)) (s : DiagramHomGauge F)

/-- 概要：局所頂点の埋め込みは Hom gauge で変わらない。
方針：対角の Hom 同定で重みを計算し、対角恒等条件を使う。
規約：KST §3.1。使われ方：捻り加群と元の加群の局所制限同型。 -/
theorem diagramGaugeDGFunctor_vertex (i : J) :
    (diagramAlgebraVertexEmbedding F i).comp (diagramGaugeDGFunctor F s) =
      diagramAlgebraVertexEmbedding F i := by
  refine EnrichedFunctor.ext (Complex R) (fun _ => rfl) ?_
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  change diagramModuleHomInclusion F (le_refl i) ≫
      (diagramGaugeHomIso F s i i).hom = diagramModuleHomInclusion F (le_refl i)
  rw [diagramGaugeHomIso_inclusion, s.scale_id]
  simp only [Iso.refl_hom, Category.id_comp]

/-- 概要：任意 raw 図式加群の gauge 制限は各局所頂点で元の加群と同型。
方針：局所埋め込みとの整合性に指定 raw 制限合成同型を適用する。
規約：KST §3.1。使われ方：大域捻り加群の局所 trivialization。 -/
def diagramGaugeLocalIso (M : RightModule R (DiagramModuleCoefficientObject F)ᵒᵖ) (i : J) :
    ForgetEnrichment.of (Complex R)
      (restrictModule R (AlgebraVertex (F.obj i))ᵒᵖ (DiagramModuleCoefficientObject F)ᵒᵖ
        (diagramAlgebraVertexEmbedding F i).op.op
        (restrictModule R _ _ (diagramGaugeDGFunctor F s).op.op M)) ≅
      ForgetEnrichment.of (Complex R)
        (restrictModule R (AlgebraVertex (F.obj i))ᵒᵖ (DiagramModuleCoefficientObject F)ᵒᵖ
          (diagramAlgebraVertexEmbedding F i).op.op M) :=
  rawTransitionRestrictionCompIso R (diagramAlgebraVertexEmbedding F i)
    (diagramGaugeDGFunctor F s) (diagramAlgebraVertexEmbedding F i)
    (diagramGaugeDGFunctor_vertex F s i) M

end SerrePositivity.KST.DerivedBlowup
