module
public import SerrePositivity.InfinityCategories.Derived.SemifreeBasisLayers

/-! # Semibasis から既存の semifree filtration へ

概要：高さ付き基底から一点 dg 加群の既存の semifree filtration を構成する。
方針：高さの段・自由商・次数付き分裂を転送し、評価の余極限反映を使う。
規約：`complexSemifree` の既存定義を使う。使われ方：semibasis 表現の十分性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.ComplexSemifreeBasis
open CategoryTheory Limits DifferentialGraded
variable {S : Type u} [CommRing S] {P : Complex S} (B : ComplexSemifreeBasis S P)

/-- 概要：高さの段を明示的な一点 dg 加群に戻す。
方針：各段の複体に `ringModule` を適用する。
規約：通常の複体としての評価は元の段。使われ方：filtration の段。 -/
abbrev moduleStage (n : ℕ) : ModuleCategory S PUnit.{1} :=
  ForgetEnrichment.of (Complex S) (ringModule S (B.stageComplex n))

/-- 概要：次の段への包含を一点 dg 加群の射に戻す。
方針：評価の充満忠実性で射を戻す。
規約：段の番号は自然数。使われ方：filtration の遷移。 -/
def moduleTransition (n : ℕ) : B.moduleStage n ⟶ B.moduleStage (n + 1) :=
  ringComplexMap S (B.stageMap (Nat.le_succ n))

/-- 概要：一点加群の段の列を評価すると元の高さ図式に一致する。
方針：隣接する遷移の一致から自然同型を作る。
規約：対象比較は恒等同型。使われ方：余極限の反映。 -/
def moduleSequenceEvaluationIso :
    Functor.ofSequence B.moduleTransition ⋙ moduleEvaluation S PUnit.{1} PUnit.unit ≅
      B.stageDiagram :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f =>
    (NatTrans.ofSequence
      (F := Functor.ofSequence B.moduleTransition ⋙ moduleEvaluation S PUnit.{1} PUnit.unit)
      (G := B.stageDiagram) (fun _ => 𝟙 _) (by
        intro n
        rw [Functor.comp_map, Functor.ofSequence_map_homOfLE_succ]
        change (moduleEvaluation S PUnit.{1} PUnit.unit).map
          (ringComplexMap S (B.stageMap (Nat.le_succ n))) ≫ 𝟙 _ =
            𝟙 _ ≫ B.stageMap (Nat.le_succ n)
        rw [ringComplexMap_evaluation, Category.comp_id, Category.id_comp])).naturality f)

/-- 概要：一点加群に戻した高さの段の cocone。
方針：各段の包含を評価の逆像で戻す。
規約：頂点は元の複体の一点加群。使われ方：filtration の網羅性。 -/
def moduleStageCocone : Cocone (Functor.ofSequence B.moduleTransition) where
  pt := ForgetEnrichment.of (Complex S) (ringModule S P)
  ι := NatTrans.ofSequence (fun n => ringComplexMap S (B.stageInclusion n)) (by
    intro n
    rw [Functor.ofSequence_map_homOfLE_succ]
    apply (moduleEvaluation S PUnit.{1} PUnit.unit).map_injective
    change (moduleEvaluation S PUnit.{1} PUnit.unit).map
      (ringComplexMap S (B.stageMap (Nat.le_succ n)) ≫
        ringComplexMap S (B.stageInclusion (n + 1))) =
      (moduleEvaluation S PUnit.{1} PUnit.unit).map (ringComplexMap S (B.stageInclusion n) ≫ 𝟙 _)
    rw [Functor.map_comp, Functor.map_comp, ringComplexMap_evaluation,
      ringComplexMap_evaluation, ringComplexMap_evaluation,
      CategoryTheory.Functor.map_id, Category.comp_id]
    exact B.stageMap_inclusion (Nat.le_succ n))

/-- 概要：一点加群の高さの段の cocone は余極限である。
方針：評価後の cocone を既知の高さの余極限と比較し、同値による余極限反映を使う。
規約：評価先の頂点は元の複体。使われ方：既存 filtration の余極限データ。 -/
def moduleStageIsColimit : IsColimit B.moduleStageCocone := by
  apply isColimitOfReflects (moduleEvaluation S PUnit.{1} PUnit.unit)
  let h := (IsColimit.precomposeHomEquiv B.moduleSequenceEvaluationIso B.stageCocone).2
    B.stageCoconeIsColimit
  apply h.ofIsoColimit
  refine Cocone.ext (Iso.refl P) (fun n => ?_)
  change (𝟙 (B.stageComplex n) ≫ B.stageInclusion n) ≫ 𝟙 P =
    (moduleEvaluation S PUnit.{1} PUnit.unit).map (ringComplexMap S (B.stageInclusion n))
  rw [Category.id_comp, Category.comp_id, ringComplexMap_evaluation]

/-- 概要：高さ付き semibasis から一点 dg 加群の semifree filtration が得られる。
方針：高さの段・自由 sphere 商・次数付き分裂・余極限を組み合わせる。
規約：既存の構造体そのものを返す。使われ方：転送定義による semifree 性の証明。 -/
def toModuleFiltration : ModuleSemifreeFiltration S PUnit.{1}
    (ForgetEnrichment.of (Complex S) (ringModule S P)) where
  stage := B.moduleStage
  transition := B.moduleTransition
  initial := B.initialSpherePresentation
  quotient n := ForgetEnrichment.of (Complex S) (ringModule S (B.layerComplex (n + 1)))
  quotientMap n := ringComplexMap S (B.layerQuotientMap n)
  split := B.layerModuleGradedSplit
  quotientPresentation n := B.layerSpherePresentation (n + 1)
  cocone := B.moduleStageCocone
  isColimit := B.moduleStageIsColimit
  iso := Iso.refl _

include B

/-- 概要：高さ付き semibasis を持つ複体は既存の意味で semifree である。
方針：実際に構成した一点加群の filtration を転送定義に代入する。
規約：semifree の定義は変更しない。使われ方：cone の semibasis からの閉性。 -/
theorem complexSemifree : SerrePositivity.InfinityCategories.complexSemifree S P :=
  ⟨B.toModuleFiltration⟩

end SerrePositivity.InfinityCategories.ComplexSemifreeBasis
