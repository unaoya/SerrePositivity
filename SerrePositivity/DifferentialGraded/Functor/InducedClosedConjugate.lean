module
public import SerrePositivity.DifferentialGraded.Category.Induced
public import SerrePositivity.KST.SConstruction.DGClosedComparisonIso
public import SerrePositivity.KST.SConstruction.DGClosedIsoConjugation
/-!
概要：任意のラベル族の間で、実 dg 関手を全次数の閉同型に沿って移す。
方針：ラベルの評価後の関手を既存の全 Hom 共役入口に渡し、標的のラベルを保持する。
規約：KST の4本の一般入口は指示された暫定依存。固有の Perf 宣言を使用しない。
使われ方：小さい提示模型の自由基底・cone・反復段階の共通 dg 作用。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w i j
namespace SerrePositivity.DifferentialGraded
open CategoryTheory SerrePositivity.KST.SConstruction
variable (A : Type u) [CommRing A] {C : Type v} {D : Type w}
  [DGCategory A C] [DGCategory A D] {I : Type i} {J : Type j}
  (source : I → C) (target : J → D) (F : DGFunctor A C D)
  (obj : I → J)
  (e : ∀ x, ForgetEnrichment.of (Complex A) (F.obj (source x)) ≅
    ForgetEnrichment.of (Complex A) (target (obj x)))

/-- 評価先の選び直しを行わず、全 Hom の共役をラベル間の dg 作用へ持ち上げる。 -/
def inducedDGFunctorClosedConjugate :
    letI := inducedDGCategory A source
    letI := inducedDGCategory A target
    DGFunctor A I J := by
  letI := inducedDGCategory A source
  letI := inducedDGCategory A target
  let L := dgFunctorClosedConjugate A ((inducedDGEvaluation A source).comp F)
    (fun x => target (obj x)) e
  exact { obj := obj
          map := L.map
          map_id := L.map_id
          map_comp := L.map_comp }

/-- 元の実関手とラベル作用の評価の比較は、全 Hom 複体に自然な閉同型。 -/
def inducedDGFunctorClosedConjugateIso :
    letI := inducedDGCategory A source
    letI := inducedDGCategory A target
    ((inducedDGEvaluation A source).comp F).onClosed ≅
      ((inducedDGFunctorClosedConjugate A source target F obj e).comp
        (inducedDGEvaluation A target)).onClosed := by
  letI := inducedDGCategory A source
  letI := inducedDGCategory A target
  refine dgFunctorClosedComparisonIso A _ _ e (fun x y => ?_)
  simpa only [DGFunctor.comp, EnrichedFunctor.comp, inducedDGEvaluation,
    inducedDGFunctorClosedConjugate, Category.comp_id] using
    dgFunctorClosedConjugate_naturality A
      ((inducedDGEvaluation A source).comp F) (fun x => target (obj x)) e x y

end SerrePositivity.DifferentialGraded
