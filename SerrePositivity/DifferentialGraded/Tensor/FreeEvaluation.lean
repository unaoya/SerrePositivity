module
public import SerrePositivity.DifferentialGraded.Tensor.KFlat
public import SerrePositivity.DifferentialGraded.Module.TensorAdjunction
public import SerrePositivity.DifferentialGraded.Complexes.Closed
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # 自由dg加群とのbalanced tensorの評価

free/evaluationとtensor/Homの随伴を合成し、同じ右随伴を持つ左随伴の一意性を使う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Limits MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 右Hom加群をxで評価すると既存のHom複体関手になる。 -/
def homRightEvaluationIso (N : LeftModule A D) (x : D) :
    homRightFunctor A D N ⋙ moduleEvaluation A D x ≅ homFunctor (N.obj x) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro T T' g
    change (moduleEvaluation A D x).map (homRightModuleMap A D N g) ≫ 𝟙 _ =
      𝟙 _ ≫ homPostcompose (N.obj x) g
    simpa only [Category.comp_id, Category.id_comp] using homRightModuleMap_eval A D N g x)

/-- 自由加群とのbalanced tensorと評価後のtensorの自然同型。 -/
def freeTensorFunctorIso (N : LeftModule A D) (x : D) :
    freeAt x ⋙ rightTensorFunctor A D N ≅ tensorRight (N.obj x) :=
  Adjunction.leftAdjointUniq
    (((freeEvaluationAdjunction A D x).comp (tensorHomAdjunction A D N)).ofNatIsoRight
      (homRightEvaluationIso A D N x))
    (tensorRightHomAdjunction (N.obj x))

/-- 自由dg加群のbalanced tensorは任意の生成複体で評価できる。 -/
def freeTensorIso (N : LeftModule A D) (x : D) (K : Complex A) :
    obj A D (ForgetEnrichment.to (Complex A) ((freeAt x).obj K)) N ≅ K ⊗ N.obj x :=
  (freeTensorFunctorIso A D N x).app K

/-- 自由加群の生成複体を変える射についての自然性。 -/
lemma freeTensorIso_naturality (N : LeftModule A D) (x : D) {K K' : Complex A} (f : K ⟶ K') :
    (rightTensorFunctor A D N).map ((freeAt x).map f) ≫ (freeTensorIso A D N x K').hom =
      (freeTensorIso A D N x K).hom ≫ (f ▷ N.obj x) :=
  (freeTensorFunctorIso A D N x).hom.naturality f

end BalancedTensor

open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- A上K-flatな生成複体からの自由加群は相対K-flat。Hom_Dのflat性は不要。 -/
lemma freeAt_relativeKFlat (x : D) (K : Complex A) (hK : complexKFlat A K) :
    moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) ((freeAt x).obj K)) := by
  intro N hN n
  exact (hK (N.obj x) (hN x) n).of_iso (BalancedTensor.freeTensorIso A D N x K).symm

end SerrePositivity.DifferentialGraded
