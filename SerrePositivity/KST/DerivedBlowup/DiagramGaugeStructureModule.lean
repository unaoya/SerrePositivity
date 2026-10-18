module

public import SerrePositivity.KST.DerivedBlowup.DiagramGaugeLocal
public import SerrePositivity.KST.DerivedBlowup.DiagramStructureRegularIso

/-!
概要：KST §3.1 の構造図式加群の一般の Hom gauge による捻り。
方針：構造加群の制限と局所 Yoneda 比較を係数図式を展開せず構成する。
規約：有限重なり Koszul 図式への適用は同じ定義の特殊化である。
使われ方：O(m) の canonical な局所比較の大域的な証明。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory Opposite DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable (F : J ⥤ Mon (Complex R)) (s : DiagramHomGauge F)

/-- 概要：指定 gauge で構造加群を捻った raw dg 加群。
方針：証明済み dg 自己関手に沿って制限する。
規約：KST §3.1。使われ方：具体的 O(m) の一般形。 -/
abbrev diagramGaugeStructureRawModule :=
  restrictModule R (DiagramModuleCoefficientObject F)ᵒᵖ (DiagramModuleCoefficientObject F)ᵒᵖ
    (diagramGaugeDGFunctor F s).op.op (diagramStructureRawModule F)

variable [Small.{u} (DiagramModuleCoefficientObject F)]

/-- 概要：指定 gauge で捻った通常の構造図式加群。
方針：raw dg 加群を閉零圏へ包む。
規約：KST §3.1。使われ方：指定局所加群比較への入力。 -/
abbrev diagramGaugeStructureModule : AllDiagramModules F :=
  ForgetEnrichment.of (Complex R) (diagramGaugeStructureRawModule F s)

/-- 概要：指定 gauge で捻った局所 raw 構造加群。
方針：局所頂点の埋め込みに沿って制限する。
規約：KST §3.1。使われ方：局所 Yoneda 拡張の値域。 -/
abbrev diagramGaugeStructureLocalRaw (i : J) :=
  restrictModule R (AlgebraVertex (F.obj i))ᵒᵖ (DiagramModuleCoefficientObject F)ᵒᵖ
    (diagramAlgebraVertexEmbedding F i).op.op (diagramGaugeStructureRawModule F s)

/-- 概要：捻りの指定局所生成元からの直接 regular 比較。
方針：構造加群と同じ局所単位を全次数 Yoneda 射へ拡張する。
規約：KST §3.1。使われ方：canonical な捻り遷移の計算。 -/
def diagramGaugeStructureLocalRegularMap (i : J) :
    ForgetEnrichment.of (Complex R) (representable R (op (.point : AlgebraVertex (F.obj i)))) ⟶
      (diagramAlgebraModuleEvaluation F i).obj (diagramGaugeStructureModule F s) :=
  representableUnitMap R (op .point) (diagramGaugeStructureLocalRaw F s i)
    (diagramStructureLocalUnit F i)

omit [Small.{u} (DiagramModuleCoefficientObject F)] in
/-- 概要：指定局所 gauge 同型の標準点成分は恒等。
方針：raw 制限比較の対象移送を、gauge が対象を固定することから消去する。
規約：KST §3.1。使われ方：直接 regular 比較の像の計算。 -/
theorem diagramGaugeStructureLocalIso_hom_eval (i : J) :
    (moduleEvaluation R (AlgebraVertex (F.obj i))ᵒᵖ (op .point)).map
      (diagramGaugeLocalIso F s (diagramStructureRawModule F) i).hom = 𝟙 _ := by
  unfold diagramGaugeLocalIso
  rw [rawTransitionRestrictionCompIso_hom_eval]
  rfl

/-- 概要：指定局所 gauge 同型は直接 regular 比較を構造加群の直接比較へ送る。
方針：Yoneda 拡張の後合成自然性と恒等評価を使う。
規約：KST §3.1。使われ方：捻りの直接比較の可逆性。 -/
theorem diagramGaugeStructureLocalRegularMap_comp (i : J) :
    diagramGaugeStructureLocalRegularMap F s i ≫
        (diagramGaugeLocalIso F s (diagramStructureRawModule F) i).hom =
      diagramStructureLocalRegularMap F i := by
  change representableUnitMap R (op .point)
      (ForgetEnrichment.to (Complex R)
        ((diagramAlgebraModuleEvaluation F i).obj (diagramGaugeStructureModule F s)))
      (diagramStructureLocalUnit F i) ≫
        (diagramGaugeLocalIso F s (diagramStructureRawModule F) i).hom = _
  rw [representableUnitMap_postcomp, diagramGaugeStructureLocalIso_hom_eval]
  change representableUnitMap R (op .point) (diagramStructureLocalRaw F i)
    (diagramStructureLocalUnit F i ≫ 𝟙 _) = _
  rw [Category.comp_id]
  rfl

-- 指定局所同型の成分を消去して直接比較の標準成分を固定する。
/-- 概要：捻りの直接 regular 比較の標準点成分は補助始点からの標準 Hom 同定。
方針：指定局所 gauge 同型を介した可換式を評価する。
規約：KST §3.1。使われ方：重み付け局所生成元と Yoneda 射の照合。 -/
theorem diagramGaugeStructureLocalRegularMap_eval (i : J) :
    (moduleEvaluation R (AlgebraVertex (F.obj i))ᵒᵖ (op .point)).map
      (diagramGaugeStructureLocalRegularMap F s i) =
      diagramModuleHomInclusion (diagramAlgebraWithBottom F)
        (bot_le : (⊥ : WithBot J) ≤ (i : WithBot J)) := by
  have he := congrArg ((moduleEvaluation R (AlgebraVertex (F.obj i))ᵒᵖ (op .point)).map)
    (diagramGaugeStructureLocalRegularMap_comp F s i)
  rw [CategoryTheory.Functor.map_comp, diagramGaugeStructureLocalIso_hom_eval] at he
  exact ((Category.comp_id _).symm.trans he).trans (diagramStructureLocalRegularMap_eval F i)

/-- 概要：捻りの直接 regular 比較は局所加群圏の同型。
方針：指定局所 gauge 同型を介して構造加群の可逆な直接比較へ戻す。
規約：KST §3.1。使われ方：指定導来 regular 比較の構成。 -/
theorem diagramGaugeStructureLocalRegularMap_isIso (i : J) :
    IsIso (diagramGaugeStructureLocalRegularMap F s i) := by
  have hc := diagramGaugeStructureLocalRegularMap_comp F s i
  let := diagramStructureLocalRegularMap_isIso F i
  have he : diagramGaugeStructureLocalRegularMap F s i =
      diagramStructureLocalRegularMap F i ≫
        (diagramGaugeLocalIso F s (diagramStructureRawModule F) i).inv := by
    rw [← hc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [he]
  infer_instance

end SerrePositivity.KST.DerivedBlowup
