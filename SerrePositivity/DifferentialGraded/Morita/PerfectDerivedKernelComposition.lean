module
public import SerrePositivity.DifferentialGraded.Morita.PerfectDerivedKernelCoherence
public import SerrePositivity.DifferentialGraded.Morita.CoherenceComposition

/-! # 公開された実際の主導来kernel合成比較のPerf制限

合成同型そのものは追加の入力を要求せず、U16aのkernelCompositionIsoを使用する。
kernel射の自然性はU16aの未完項目なので、対応する図式を明示して受け取る。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (B : Type z) [DGCategory A B] [Small.{u} B]
  (hD : localHomKFlat A D) (P : Kernel A D E) (Q : Kernel A E B)
  (hP : kernelColumnsPerfect A D E P) (hQ : kernelColumnsPerfect A E B Q)
include hP hQ

lemma kernelCompose_columnsPerfect_of_columns :
    kernelColumnsPerfect A D B (kernelCompose A D E B hD P Q) :=
  kernelCompose_columnsPerfect A D E B hD P Q hP hQ (kernelCompositionIso A D E B hD P Q)

def perfectKernelCompositionIso :
    perfectDerivedKernelAction A D E P hP ⋙ perfectDerivedKernelAction A E B Q hQ ≅
      perfectDerivedKernelAction A D B (kernelCompose A D E B hD P Q)
        (kernelCompose_columnsPerfect_of_columns A D E B hD P Q hP hQ) :=
  perfectDerivedKernelCompositionIso A D E B hD P Q hP hQ
    (kernelCompositionIso A D E B hD P Q)

lemma perfectKernelCompositionIso_inclusion :
    Functor.whiskerRight (perfectKernelCompositionIso A D E B hD P Q hP hQ).hom
        (perfectModuleInclusion A B Set.univ) =
      Functor.whiskerLeft (perfectModuleInclusion A D Set.univ)
        (kernelCompositionIso A D E B hD P Q).hom :=
  perfectDerivedKernelCompositionIso_inclusion A D E B hD P Q hP hQ
    (kernelCompositionIso A D E B hD P Q)

lemma perfectKernelCompositionIso_naturality
    (P' : Kernel A D E) (Q' : Kernel A E B)
    (hP' : kernelColumnsPerfect A D E P') (hQ' : kernelColumnsPerfect A E B Q')
    (f : P ⟶ P') (g : Q ⟶ Q')
    (hNat : NatTrans.hcomp ((kernelDerivedTensorFunctor A D E).map f)
        ((kernelDerivedTensorFunctor A E B).map g) ≫
        (kernelCompositionIso A D E B hD P' Q').hom =
      (kernelCompositionIso A D E B hD P Q).hom ≫
        (kernelDerivedTensorFunctor A D B).map (kernelComposeMap A D E B hD f g)) :
    NatTrans.hcomp (perfectDerivedKernelMap A D E hP hP' f)
        (perfectDerivedKernelMap A E B hQ hQ' g) ≫
        (perfectKernelCompositionIso A D E B hD P' Q' hP' hQ').hom =
      (perfectKernelCompositionIso A D E B hD P Q hP hQ).hom ≫
        perfectDerivedKernelMap A D B
          (kernelCompose_columnsPerfect_of_columns A D E B hD P Q hP hQ)
          (kernelCompose_columnsPerfect_of_columns A D E B hD P' Q' hP' hQ')
          (kernelComposeMap A D E B hD f g) :=
  perfectDerivedKernelCompositionIso_naturality A D E B hD P Q hP hQ
    (kernelCompositionIso A D E B hD P Q) P' Q' hP' hQ'
    (kernelCompositionIso A D E B hD P' Q') f g hNat

/-- 実際の合成比較は、両kernelの任意の主導来射に対してPerf上でも自然。 -/
lemma perfectKernelCompositionIso_kernel_naturality
    (P' : Kernel A D E) (Q' : Kernel A E B)
    (hP' : kernelColumnsPerfect A D E P') (hQ' : kernelColumnsPerfect A E B Q')
    (f : P ⟶ P') (g : Q ⟶ Q') :
    NatTrans.hcomp (perfectDerivedKernelMap A D E hP hP' f)
        (perfectDerivedKernelMap A E B hQ hQ' g) ≫
        (perfectKernelCompositionIso A D E B hD P' Q' hP' hQ').hom =
      (perfectKernelCompositionIso A D E B hD P Q hP hQ).hom ≫
        perfectDerivedKernelMap A D B
          (kernelCompose_columnsPerfect_of_columns A D E B hD P Q hP hQ)
          (kernelCompose_columnsPerfect_of_columns A D E B hD P' Q' hP' hQ')
          (kernelComposeMap A D E B hD f g) :=
  perfectKernelCompositionIso_naturality A D E B hD P Q hP hQ P' Q' hP' hQ' f g
    (kernelCompositionIso_naturality A D E B hD f g)

end SerrePositivity.DifferentialGraded.Morita
