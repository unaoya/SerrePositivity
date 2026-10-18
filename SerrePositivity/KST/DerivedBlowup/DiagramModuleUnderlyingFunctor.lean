module

public import SerrePositivity.KST.DerivedBlowup.DiagramModuleUnderlyingDiagram
public import SerrePositivity.KST.DerivedBlowup.TransitionModuleNaturality
public import SerrePositivity.DifferentialGraded.Module.QuasiIso

/-!
概要：KST §3.1 の図式 dg 加群の射を underlying 複体図式の自然変換へ送る。
方針：加群射の全次数自然性を指定単位矢で評価し、各頂点の評価を束ねる。
規約：単なる複体図式の擬同型性を cartesian 条件とは同一視しない。
使われ方：図式全体の置換と局所比較の自然性を通常の図式へ接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open DifferentialGraded

variable {R : Type u} [CommRing R]

/-- 概要：単位からの任意の指定閉矢の加群作用は加群射について自然。
方針：全次数 Hom 自然性に指定矢を前合成し、通常鎖写像へ戻す。
規約：KST §3.1。使われ方：指定単位矢の underlying 自然変換。 -/
theorem moduleClosedArrowAction_natural {D : Type w} [DGCategory R D] [Small.{u} D]
    {M N : ModuleCategory R Dᵒᵖ} (f : M ⟶ N) {x y : D}
    (t : 𝟙_ (Complex R) ⟶ homObject R D x y) :
    (moduleEvaluation R Dᵒᵖ (op x)).map f ≫
        mapFromUnit R _ _ (t ≫ (ForgetEnrichment.to (Complex R) N).map (op (op x))
          (op (op y))) =
      mapFromUnit R _ _ (t ≫ (ForgetEnrichment.to (Complex R) M).map (op (op x))
        (op (op y))) ≫ (moduleEvaluation R Dᵒᵖ (op y)).map f := by
  change (moduleEvaluation R Dᵒᵖ (op x)).map f ≫
      mapFromUnit R ((ForgetEnrichment.to (Complex R) N).obj (op (op x)))
        ((ForgetEnrichment.to (Complex R) N).obj (op (op y)))
        (t ≫ (ForgetEnrichment.to (Complex R) N).map (op (op x)) (op (op y))) =
    mapFromUnit R ((ForgetEnrichment.to (Complex R) M).obj (op (op x)))
      ((ForgetEnrichment.to (Complex R) M).obj (op (op y)))
      (t ≫ (ForgetEnrichment.to (Complex R) M).map (op (op x)) (op (op y))) ≫
        (moduleEvaluation R Dᵒᵖ (op y)).map f
  have h := closedTransApp_naturality R (moduleClosedHomEquiv R Dᵒᵖ M N f)
    (op (op x)) (op (op y))
  rw [moduleClosedHomEquiv_app, moduleClosedHomEquiv_app] at h
  have hh := congrArg (fun s => t ≫ s) h
  have hm := congrArg (fun s => mapFromUnit R
    ((ForgetEnrichment.to (Complex R) M).obj (op (op x)))
    ((ForgetEnrichment.to (Complex R) N).obj (op (op y))) s) hh
  simpa only [← Category.assoc, mapFromUnit_postcompose, mapFromUnit_precompose] using hm.symm

variable {J : Type v} [Preorder J] [DecidableLE J]
variable (F : J ⥤ Mon (Complex R)) [Small.{u} (DiagramModuleCoefficientObject F)]

/-- 概要：図式加群射を underlying 複体図式の自然変換へ送る。
方針：成分は頂点での加群評価、自然性は指定単位矢での全次数自然性。
規約：KST §3.1。使われ方：図式全体の置換と underlying 図式の比較。 -/
def diagramModuleUnderlyingMap {M N : AllDiagramModules F} (f : M ⟶ N) :
    diagramModuleUnderlyingDiagram F (ForgetEnrichment.to (Complex R) M) ⟶
      diagramModuleUnderlyingDiagram F (ForgetEnrichment.to (Complex R) N) where
  app i := (moduleEvaluation R (DiagramModuleCoefficientObject F)ᵒᵖ (op ⟨i⟩)).map f
  naturality i j h := by
    change (diagramModuleUnderlyingDiagram F (ForgetEnrichment.to (Complex R) M)).map
        (homOfLE (leOfHom h)) ≫
        (moduleEvaluation R (DiagramModuleCoefficientObject F)ᵒᵖ (op ⟨j⟩)).map f =
      (moduleEvaluation R (DiagramModuleCoefficientObject F)ᵒᵖ (op ⟨i⟩)).map f ≫
        (diagramModuleUnderlyingDiagram F (ForgetEnrichment.to (Complex R) N)).map
          (homOfLE (leOfHom h))
    rw [diagramModuleUnderlyingDiagram_map, diagramModuleUnderlyingDiagram_map]
    exact (moduleClosedArrowAction_natural f (diagramModuleTransitionUnit F (leOfHom h))).symm

/-- 概要：全図式 dg 加群圏から underlying 複体図式圏への実際の関手。
方針：対象図式と構成済み自然変換を束ね、恒等・合成を各頂点で確認する。
規約：KST §3.1。使われ方：全図式の弱同値の underlying 検査。 -/
def diagramModuleUnderlyingFunctor : AllDiagramModules F ⥤ (J ⥤ Complex R) where
  obj M := diagramModuleUnderlyingDiagram F (ForgetEnrichment.to (Complex R) M)
  map f := diagramModuleUnderlyingMap F f
  map_id M := by
    apply NatTrans.ext
    funext i
    exact CategoryTheory.Functor.map_id
      (moduleEvaluation R (DiagramModuleCoefficientObject F)ᵒᵖ (op ⟨i⟩)) M
  map_comp f g := by
    apply NatTrans.ext
    funext i
    exact CategoryTheory.Functor.map_comp
      (moduleEvaluation R (DiagramModuleCoefficientObject F)ᵒᵖ (op ⟨i⟩)) f g

/-- 概要：図式加群の擬同型は underlying 複体図式の各頂点で検出される。
方針：係数圏の対象が図式の添字そのものであることを使う。
規約：KST §3.1、これは置換の弱同値の判定であり cartesian 条件ではない。
使われ方：全図式の導来局所化を underlying 図式へ送る際の入力。 -/
theorem diagramModuleUnderlyingFunctor_quasiIso_iff {M N : AllDiagramModules F} (f : M ⟶ N) :
    moduleQuasiIso R (DiagramModuleCoefficientObject F)ᵒᵖ f ↔
      ∀ i : J, QuasiIso (((diagramModuleUnderlyingFunctor F).map f).app i) := by
  constructor
  · intro hf i
    exact hf (op ⟨i⟩)
  · intro hf x
    exact hf x.unop.index

end SerrePositivity.KST.DerivedBlowup
