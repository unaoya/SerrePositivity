module

public import SerrePositivity.KST.DerivedBlowup.DiagramStructureLocalComparison
public import SerrePositivity.KST.DerivedBlowup.RepresentableUnitNaturality

/-!
概要：KST §3.1 の構造加群の局所 regular 比較を直接の Yoneda 射として指定する。
方針：補助始点からの単位矢を局所構造加群へ拡張し、構成済み反復制限比較で検証する。
規約：後の随伴計算で使う比較射そのものを指定する。
使われ方：構造加群の canonical な cartesian 比較との可換式。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable (F : J ⥤ Mon (Complex R)) [Small.{u} (DiagramModuleCoefficientObject F)]

/-- 概要：構造図式加群の局所 raw dg 加群。
方針：正規表示の局所埋め込みに沿って構成済み構造加群を制限する。
規約：KST §3.1。使われ方：直接 Yoneda 比較の値域。 -/
abbrev diagramStructureLocalRaw (i : J) : RightModule R (AlgebraVertex (F.obj i))ᵒᵖ :=
  restrictModule R (AlgebraVertex (F.obj i))ᵒᵖ (DiagramModuleCoefficientObject F)ᵒᵖ
    (diagramAlgebraVertexEmbedding F i).op.op (diagramStructureRawModule F)

/-- 概要：局所構造加群の指定閉零の生成元。
方針：補助始点から元の局所頂点への指定包含単位を使う。
規約：KST §3.1。使われ方：直接の局所 regular Yoneda 比較。 -/
def diagramStructureLocalUnit (i : J) :
    𝟙_ (Complex R) ⟶ (diagramStructureLocalRaw F i).obj (op (op .point)) :=
  diagramModuleTransitionUnit (diagramAlgebraWithBottom F)
    (bot_le : (⊥ : WithBot J) ≤ (i : WithBot J))

/-- 概要：局所 regular 代表から実際の局所構造加群への指定 Yoneda 射。
方針：補助始点の単位生成元を全次数自然な射へ拡張する。
規約：KST §3.1。使われ方：canonical な局所係数拡大比較の計算。 -/
def diagramStructureLocalRegularMap (i : J) :
    ForgetEnrichment.of (Complex R) (representable R (op (.point : AlgebraVertex (F.obj i)))) ⟶
      (diagramAlgebraModuleEvaluation F i).obj (diagramStructureModule F) :=
  representableUnitMap R (op .point) (diagramStructureLocalRaw F i) (diagramStructureLocalUnit F i)

/-- 概要：構造加群の反復・直接局所制限比較の標準点成分は恒等。
方針：raw 制限合成同型の成分公式の対象移送を簡約する。
規約：KST §3.1。使われ方：局所生成元の同定。 -/
theorem diagramStructureLocalComparisonIso_hom_eval (i : J) :
    (moduleEvaluation R (AlgebraVertex (F.obj i))ᵒᵖ (op .point)).map
      (diagramStructureLocalComparisonIso F i).hom = 𝟙 _ := by
  change (moduleEvaluation R (AlgebraVertex (F.obj i))ᵒᵖ (op .point)).map
    (rawTransitionRestrictionCompIso R (diagramAlgebraVertexEmbedding F i)
      (diagramAlgebraBottomInclusion F)
      (diagramAlgebraVertexEmbedding (diagramAlgebraWithBottom F) (i : WithBot J))
      (diagramAlgebraBottomInclusion_vertex F i)
      (representable R
        (op (⟨⊥⟩ : DiagramModuleCoefficientObject (diagramAlgebraWithBottom F))))).hom = _
  rw [rawTransitionRestrictionCompIso_hom_eval]
  rfl

/-- 概要：直接 Yoneda 比較は反復制限比較を介して補助 representable の比較と一致する。
方針：Yoneda 射の後合成自然性と局所生成元の恒等成分を使う。
規約：KST §3.1。使われ方：直接指定した比較の擬同型性。 -/
theorem diagramStructureLocalRegularMap_comp (i : J) :
    diagramStructureLocalRegularMap F i ≫ (diagramStructureLocalComparisonIso F i).hom =
      diagramRepresentableLocalRegularMap (diagramAlgebraWithBottom F)
        (bot_le : (⊥ : WithBot J) ≤ (i : WithBot J)) := by
  change representableUnitMap R (op .point)
      (ForgetEnrichment.to (Complex R)
        ((diagramAlgebraModuleEvaluation F i).obj (diagramStructureModule F)))
      (diagramStructureLocalUnit F i) ≫ (diagramStructureLocalComparisonIso F i).hom = _
  rw [representableUnitMap_postcomp, diagramStructureLocalComparisonIso_hom_eval]
  change representableUnitMap R (op .point)
      (diagramRepresentableLocalRaw (diagramAlgebraWithBottom F) ⊥ (i : WithBot J))
      (diagramStructureLocalUnit F i ≫ 𝟙 _) = _
  rw [Category.comp_id]
  rfl

/-- 概要：構造加群への直接局所 regular 比較は objectwise 擬同型。
方針：構成済み補助 representable 比較の擬同型性と制限合成同型を使う。
規約：KST §3.1。使われ方：指定比較射を主導来局所化で反転する。 -/
theorem diagramStructureLocalRegularMap_quasiIso (i : J) :
    moduleQuasiIso R (AlgebraVertex (F.obj i))ᵒᵖ (diagramStructureLocalRegularMap F i) := by
  have hg : moduleQuasiIso R (AlgebraVertex (F.obj i))ᵒᵖ
      (diagramStructureLocalComparisonIso F i).hom := fun _ => by infer_instance
  have hc : moduleQuasiIso R (AlgebraVertex (F.obj i))ᵒᵖ
      (diagramStructureLocalRegularMap F i ≫ (diagramStructureLocalComparisonIso F i).hom) := by
    rw [diagramStructureLocalRegularMap_comp]
    exact diagramRepresentableLocalRegularMap_quasiIso (diagramAlgebraWithBottom F)
      (bot_le : (⊥ : WithBot J) ≤ (i : WithBot J))
  exact (moduleQuasiIso R (AlgebraVertex (F.obj i))ᵒᵖ).of_postcomp _ _ hg hc

end SerrePositivity.KST.DerivedBlowup
