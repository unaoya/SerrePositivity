module
public import SerrePositivity.DifferentialGraded.Verdier.GraphPerfectSquare
public import SerrePositivity.DifferentialGraded.Morita.KernelResolution

/-! # U16a の実際の通常 graph kernel 作用と dg 商の比較

通常 bimodule 上の主導来作用を使用する。主導来 kernel 全体の未実装の作用は仮定しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Morita
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)
  (S : Set D) (T : Set E) (hF : ∀ d ∈ S, F.obj d ∈ T)

/-- 元の dg 関手と誘導商関手の graph kernel の、全導来対象・射に自然な正方形。 -/
def graphKernelQuotientSquare :
    kernelDerivedTensorOnBimodule A D (QuotientObject D S)
        (functorGraph A D (QuotientObject D S) (inclusion A D S)) ⋙
      kernelDerivedTensorOnBimodule A (QuotientObject D S) (QuotientObject E T)
        (functorGraph A (QuotientObject D S) (QuotientObject E T)
          (quotientDGFunctor A D E F S T hF)) ≅
    kernelDerivedTensorOnBimodule A D E (functorGraph A D E F) ⋙
      kernelDerivedTensorOnBimodule A E (QuotientObject E T)
        (functorGraph A E (QuotientObject E T) (inclusion A E T)) :=
  graphDerivedQuotientSquare A D E F S T hF

lemma graphKernelQuotientSquare_naturality
    {X Y : DerivedModuleCategory A D} (f : X ⟶ Y) :
    (dgDerivedExtension A D (QuotientObject D S) (inclusion A D S) ⋙
        dgDerivedExtension A (QuotientObject D S) (QuotientObject E T)
          (quotientDGFunctor A D E F S T hF)).map f ≫
        (graphKernelQuotientSquare A D E F S T hF).hom.app Y =
      (graphKernelQuotientSquare A D E F S T hF).hom.app X ≫
        (dgDerivedExtension A D E F ⋙
          dgDerivedExtension A E (QuotientObject E T) (inclusion A E T)).map f :=
  (graphKernelQuotientSquare A D E F S T hF).hom.naturality f
end SerrePositivity.DifferentialGraded.DGQuotient
