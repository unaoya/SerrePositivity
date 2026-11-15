module
public import SerrePositivity.EInfinity.Modules.TensorHomEvaluation
public import SerrePositivity.EInfinity.Modules.TensorHomPinched
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorPinchedIso

/-!
概要：同じ全加群 frame の評価は元の Dold–Kan・pinched 座標と可換。
方針：同じ Dold–Kan 評価式と任意 Hom 鎖写像への既存の自然性を合成する。
規約：HA 1.3.1.13、Kerodon 2.5.9（Tag 00SC）、全単体。
使われ方：M10 の BE の小さい底の元の全三相 cochain の評価比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory Opposite
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories
variable (A : Type u) [CommRing A] (D : Type) [DGCategory A D] [Small.{u} D]

/-- 概要：同じ frame Hom の全評価は同じ主 Hom end の pinched 評価。
方針：元の二つの全座標同型と Hom 鎖写像の自然性を貼り合わせる。
規約：HA 1.3.1.13、全次数。使われ方：元の pinched 単体の実評価。 -/
lemma moduleTensorHomPinchedIso_evaluation (P Q : ModuleCategory A D) (x : D) :
    SSet.uliftFunctor.{u + 1, u}.map (moduleTensorEvaluationHomMap A D P Q x) ≫
      (normalizedTensorPinchedIso A ((moduleEvaluation A D x).obj P)
        ((moduleEvaluation A D x).obj Q)).hom =
    SSet.uliftFunctor.{u + 1, u}.map (moduleTensorHomDoldKanIso A D P Q).hom ≫
      (moduleDoldKanPinchedIso A D P Q).hom ≫
        pinchedHomChainMap (moduleHomπ A D (ForgetEnrichment.to (Complex A) P)
          (ForgetEnrichment.to (Complex A) Q) x) := by
  dsimp only [normalizedTensorPinchedIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← SSet.uliftFunctor.map_comp,
    ← moduleTensorHomDoldKanIso_evaluation, SSet.uliftFunctor.map_comp, Category.assoc]
  have h := doldKanHomPinchedIso_chainMap (R := A) (D := RightModule A D) (E := Complex A)
    (x := ForgetEnrichment.to (Complex A) P)
    (y := ForgetEnrichment.to (Complex A) Q)
    (x' := (ForgetEnrichment.to (Complex A) P).obj (op x))
    (y' := (ForgetEnrichment.to (Complex A) Q).obj (op x))
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) P)
      (ForgetEnrichment.to (Complex A) Q) x)
  exact congrArg (fun f => SSet.uliftFunctor.{u + 1, u}.map
    (moduleTensorHomDoldKanIso A D P Q).hom ≫ f) h

end SerrePositivity.EInfinity.Modules
