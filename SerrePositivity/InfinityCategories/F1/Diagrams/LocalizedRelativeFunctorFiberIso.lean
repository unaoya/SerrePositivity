module

public import SerrePositivity.InfinityCategories.F1.Diagrams.LocalizedRelativeFunctorPullback
public import SerrePositivity.InfinityCategories.F1.Fibrations.VertexFiberIsPullbackIso

/-!
概要：局所化後の全空間の指定底 fiber を、元の相対関手空間へ厳密に戻す。
方針：二つの実 pullback の fiber 同型と、底関手の頂点の等号を合成する。
規約：元の相対関手空間への包含を全単体で回収する。
使われ方：全空間比較の fiber 同値を、指定された相対前合成自身に移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 底の頂点の等号移送は、元の fiber 包含を保持する。 -/
lemma vertexFiber_eqTransport_ι {E B : SSet.{u}} (p : E ⟶ B)
    {a b : B _⦋0⦌} (h : a = b) :
    (eqToIso (congrArg (vertexFiber p) h)).hom ≫ vertexFiberι p b = vertexFiberι p a := by
  cases h
  rfl

variable {N A E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
  (f : N ⟶ A) (W : Set (N _⦋1⦌)) (hf : InvertsEdges f W)
  (p : E ⟶ B) [LeftFibration p] (b : A ⟶ B)

/-- 局所化した底頂点の包含像は、元の前合成の底頂点である。 -/
lemma localizationInvertingBaseVertex :
    (invertingFunctors N B W).ι.app (Opposite.op ⦋0⦌)
      ((localizationPrecomposition f W hf B).app (Opposite.op ⦋0⦌) (functorVertex b)) =
        functorVertex (f ≫ b) := by
  exact congrArg (fun k => k.app (Opposite.op ⦋0⦌) (functorVertex b))
    (localizationPrecomposition_ι f W hf B)

/-- 指定底上の全空間 fiber と、元の相対関手空間の厳密な同型。 -/
def localizationRelativeFiberIso :
    vertexFiber (localizationRelativeProjection f W hf p) (functorVertex b) ≅
      relativeFunctorSpace p (f ≫ b) :=
  vertexFiberIsoOfIsPullback (IsPullback.of_hasPullback
      (localizationPrecomposition f W hf B) (invertingFunctorPostcomp p W)).flip
        (functorVertex b) ≪≫
    vertexFiberIsoOfIsPullback (invertingFunctorPostcomp_isPullback p W)
      ((localizationPrecomposition f W hf B).app (Opposite.op ⦋0⦌) (functorVertex b)) ≪≫
    eqToIso (congrArg (vertexFiber ((ihom N).map p))
      (localizationInvertingBaseVertex f W hf b))

/-- 同じ fiber 同型は元の全関手圏への包含を厳密に保つ。 -/
lemma localizationRelativeFiberIso_hom_ι :
    (localizationRelativeFiberIso f W hf p b).hom ≫
      vertexFiberι ((ihom N).map p) (functorVertex (f ≫ b)) =
        vertexFiberι (localizationRelativeProjection f W hf p) (functorVertex b) ≫
          pullback.snd (localizationPrecomposition f W hf B) (invertingFunctorPostcomp p W) ≫
            (invertingFunctors N E W).ι := by
  simp only [localizationRelativeFiberIso, Iso.trans_hom, Category.assoc]
  rw [vertexFiber_eqTransport_ι ((ihom N).map p) (localizationInvertingBaseVertex f W hf b)]
  rw [vertexFiberIsoOfIsPullback_hom_ι, ← Category.assoc,
    vertexFiberIsoOfIsPullback_hom_ι, Category.assoc]
  rfl

end SerrePositivity.InfinityCategories
