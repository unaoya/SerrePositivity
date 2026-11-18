module
public import SerrePositivity.EInfinity.Modules.TensorDoldKanHom

/-!
概要：加群の元の全 frame Hom を対象ごとの複体の frame Hom へ評価する。
方針：同じテンソル射の評価と転置の評価式を全単体に束ねる。
規約：HA 1.3.1.13、全次元・全単体作用素。
使われ方：M10 の元の全三角形と複体側の全評価三角形の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory Opposite
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 概要：元の加群 frame の全単体射を同じ対象で評価する。
方針：テンソル単体の評価は複体の元の frame そのもの。
規約：HA 1.3.1.13、退化も含む。使われ方：全要素圏の評価。 -/
def moduleTensorEvaluationHomMap (P Q : ModuleCategory A D) (x : D) :
    (cosimplicialHom ((moduleTensorSimplicesFunctor A D).obj P)).obj Q ⟶
      (cosimplicialHom (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A ((moduleEvaluation A D x).obj P))).obj
        ((moduleEvaluation A D x).obj Q) :=
  (moduleTensorHomDoldKanIso A D P Q).hom ≫
    (_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map
      (moduleHomπ A D (ForgetEnrichment.to (Complex A) P)
        (ForgetEnrichment.to (Complex A) Q) x) ≫
    (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorHomIso A ((moduleEvaluation A D x).obj P)
      ((moduleEvaluation A D x).obj Q)).inv

/-- 概要：同じ全 frame Hom の評価と同じ Dold–Kan 同型は可換。
方針：全単体で元の転置の評価式と正規化 Hom 同値の自然性を使う。
規約：HA 1.3.1.13、主 Hom end の評価。使われ方：全普遍係数の比較。 -/
lemma moduleTensorHomDoldKanIso_evaluation (P Q : ModuleCategory A D) (x : D) :
    (moduleTensorHomDoldKanIso A D P Q).hom ≫
      (_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map
        (moduleHomπ A D (ForgetEnrichment.to (Complex A) P)
          (ForgetEnrichment.to (Complex A) Q) x) =
      moduleTensorEvaluationHomMap A D P Q x ≫
        (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorHomIso A ((moduleEvaluation A D x).obj P)
          ((moduleEvaluation A D x).obj Q)).hom := by
  simp only [moduleTensorEvaluationHomMap, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- 概要：同じ全評価写像の転置は元の加群射を評価した右転置。
方針：元の二つの Hom 同値の両逆と転置の評価式を使う。
規約：HA 1.3.1.13、左右のテンソル順序を保持。使われ方：全係数の比較。 -/
lemma moduleTensorEvaluationHomMap_transpose (P Q : ModuleCategory A D) (x : D)
    (n : SimplexCategory)
    (f : ((moduleTensorSimplicesFunctor A D).obj P).obj n ⟶ Q) :
    _root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorHomEquiv A ((moduleEvaluation A D x).obj P)
      ((moduleEvaluation A D x).obj Q) n
      ((moduleTensorEvaluationHomMap A D P Q x).app (op n) f) =
    _root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A _ n (curryRight ((moduleEvaluation A D x).map f)) := by
  change _root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorHomEquiv A _ _ n
    ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorHomEquiv A _ _ n).symm
      (((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map
        (moduleHomπ A D (ForgetEnrichment.to (Complex A) P)
          (ForgetEnrichment.to (Complex A) Q) x)).app (op n)
        (_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A _ n (moduleParamCurry A D f)))) = _
  rw [Equiv.apply_symm_apply]
  exact (_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv_postcomp A n (moduleParamCurry A D f)
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) P)
      (ForgetEnrichment.to (Complex A) Q) x)).symm.trans
        (congrArg (_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A _ n) (moduleParamCurry_π A D f x))

end SerrePositivity.EInfinity.Modules
