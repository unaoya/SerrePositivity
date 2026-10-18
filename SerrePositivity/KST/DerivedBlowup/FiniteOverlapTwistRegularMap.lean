module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapTwistLocal
public import SerrePositivity.KST.DerivedBlowup.DiagramStructureRegularIso
public import SerrePositivity.KST.DerivedBlowup.DiagramGaugeRegularIso
public import SerrePositivity.KST.DerivedBlowup.DiagramGaugeStructureModule

/-!
概要：KST §3.1 の捻り対象への局所 regular 比較を直接の Yoneda 射として指定する。
方針：構造加群と同じ局所生成元を拡張し、指定局所 trivialization の成分で検証する。
規約：後続の随伴計算で使う射自体を固定する。
使われ方：O(m) の canonical な係数拡大比較の可逆性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory Opposite DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：実際の捻り加群を局所頂点へ制限した raw dg 加群。
方針：正規表示の局所埋め込みに沿って制限する。
規約：KST §3.1。使われ方：局所 Yoneda 拡張の値域。 -/
abbrev finiteOverlapTwistLocalRaw (a : I → R) (m : ℤ) (T : FiniteOverlapIndex I) :=
  restrictModule R (AlgebraVertex ((finiteOverlapDGAlgebraDiagram R a).obj T))ᵒᵖ
    (DiagramModuleCoefficientObject (finiteOverlapDGAlgebraDiagram R a))ᵒᵖ
    (diagramAlgebraVertexEmbedding (finiteOverlapDGAlgebraDiagram R a) T).op.op
    (finiteOverlapTwistRawModule R a m)

/-- 概要：指定捻り加群の局所閉零生成元。
方針：捻りは局所の値を保つので構造加群の指定生成元を使う。
規約：KST §3.1。使われ方：直接 regular 比較を Yoneda 拡張する。 -/
def finiteOverlapTwistLocalUnit (a : I → R) (m : ℤ) (T : FiniteOverlapIndex I) :
    𝟙_ (Complex R) ⟶ (finiteOverlapTwistLocalRaw R a m T).obj (op (op .point)) :=
  diagramStructureLocalUnit (finiteOverlapDGAlgebraDiagram R a) T

/-- 概要：指定生成元を拡張した捻り加群への直接 regular 比較。
方針：全次数自然な閉零 Yoneda 拡張を使う。
規約：KST §3.1。使われ方：捻りの canonical な比較射の計算。 -/
def finiteOverlapTwistLocalRegularMap (a : I → R) (m : ℤ) (T : FiniteOverlapIndex I) :
    ForgetEnrichment.of (Complex R)
        (representable R
          (op (.point : AlgebraVertex ((finiteOverlapDGAlgebraDiagram R a).obj T)))) ⟶
      (diagramAlgebraModuleEvaluation (finiteOverlapDGAlgebraDiagram R a) T).obj
        (finiteOverlapTwistModule R a m) :=
  representableUnitMap R (op .point) (finiteOverlapTwistLocalRaw R a m T)
    (finiteOverlapTwistLocalUnit R a m T)

/-- 概要：捻りの指定局所 trivialization の標準点成分は恒等。
方針：raw 制限比較の評価公式と、対象写像が恒等であることを使う。
規約：KST §3.1。使われ方：直接 Yoneda 比較を構造加群の比較へ戻す。 -/
theorem finiteOverlapTwistLocalIso_hom_eval (a : I → R) (m : ℤ) (T : FiniteOverlapIndex I) :
    (moduleEvaluation R (AlgebraVertex ((finiteOverlapDGAlgebraDiagram R a).obj T))ᵒᵖ
      (op .point)).map (finiteOverlapTwistLocalIso R a m T).hom = 𝟙 _ := by
  unfold finiteOverlapTwistLocalIso diagramGaugeLocalIso
  rw [rawTransitionRestrictionCompIso_hom_eval]
  rfl

/-- 概要：直接 regular 比較は指定局所 trivialization を介して構造加群の比較に一致。
方針：Yoneda 拡張の後合成自然性と恒等成分を使う。
規約：KST §3.1。使われ方：直接指定した比較の可逆性と生成元の追跡。 -/
theorem finiteOverlapTwistLocalRegularMap_comp (a : I → R) (m : ℤ)
    (T : FiniteOverlapIndex I) :
    finiteOverlapTwistLocalRegularMap R a m T ≫ (finiteOverlapTwistLocalIso R a m T).hom =
      diagramStructureLocalRegularMap (finiteOverlapDGAlgebraDiagram R a) T :=
  diagramGaugeStructureLocalRegularMap_comp (finiteOverlapDGAlgebraDiagram R a)
    (finiteOverlapTwistGauge R a m) T

/-- 概要：直接 regular 比較は局所加群圏の同型。
方針：構造加群への指定比較と局所 trivialization の可逆性で消去する。
規約：KST §3.1。使われ方：canonical な係数拡大比較を移す局所同型。 -/
theorem finiteOverlapTwistLocalRegularMap_isIso (a : I → R) (m : ℤ)
    (T : FiniteOverlapIndex I) : IsIso (finiteOverlapTwistLocalRegularMap R a m T) := by
  have hc := finiteOverlapTwistLocalRegularMap_comp R a m T
  let := diagramStructureLocalRegularMap_isIso (finiteOverlapDGAlgebraDiagram R a) T
  have he : finiteOverlapTwistLocalRegularMap R a m T =
      diagramStructureLocalRegularMap (finiteOverlapDGAlgebraDiagram R a) T ≫
        (finiteOverlapTwistLocalIso R a m T).inv := by
    rw [← hc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [he]
  infer_instance

end SerrePositivity.KST.DerivedBlowup
