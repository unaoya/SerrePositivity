module

public import SerrePositivity.EInfinity.FrameHom.RightFrameSpecifiedLocalization
public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantLocalization

/-!
概要：指定 right frame と第一分解から指定局所化比較への残る入力を全圏普遍性一つに絞る。
方針：第一分解から source frame を選び、同じ六辺と同じ指定二胞体へ代入する。
規約：全圏の hammock 普遍性は Ind-S (6) の源移送を待つ明示入力である。
使われ方：その公開定理を代入した条件なしの主入口の構成。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory HomotopicalAlgebra SSet Opposite
open SerrePositivity.Reedy SerrePositivity.InfinityCategories
open scoped Simplicial
attribute [local instance] FrameHom.rightFrameHom_kanComplex
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [(cofibrations C).HasFunctorialFactorization (trivialFibrations C)]
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)
  {Q : SSet.{max u v}} [Quasicategory Q]
  (G : nerve (modelRelativeCategory C).category ⟶ Q)
  (hG : IsLocalization G (weakNerveEdges (modelRelativeCategory C)))
  (hH : IsLocalization (hammockLocalizationNerveMap (modelRelativeCategory C))
    (weakNerveEdges (modelRelativeCategory C)))
  (K : kanHammockNerve (modelRelativeCategory C) ⟶ Q)
  (e : FunctorIso (hammockLocalizationNerveMap (modelRelativeCategory C) ≫ K) G)
  (X : C) [IsCofibrant X]

/-- 概要：第一分解から選んだ同じ source frame による全 right frame 比較。
方針：全六辺の coherent 関手同型を元の全標的図式で回収する。
規約：source frame の追加存在入力なし。使われ方：指定局所化比較の全図式側。 -/
def modelRightFrameHammockCoherentComparison :
    FunctorIso
      (FrameHom.rightFrameHammockCoherentDiagram
        ((modelSourceFrameFamily (C := C)).atObject X) r 0)
      (FrameHom.rightFrameHammockCoherentDiagram
        ((modelSourceFrameFamily (C := C)).atObject X) r 6) :=
  FrameHom.rightFrameHammockCoherentComparison ((modelSourceFrameFamily (C := C)).atObject X)
    r (MorphismProperty.functorialFactorizationData _ _)

/-- 概要：同じ指定二胞体を保持した全標的の実 pinched Hom 比較。
方針：同じ第一分解から選んだ source frame と同じ六辺へ実データを代入する。
規約：残る入力は全圏 hammock の普遍性。使われ方：源移送供給後の条件の放電。 -/
def modelRightFrameSpecifiedPinchedEquivalence (Y : C) :
    QCatEquivalence
      (SSet.uliftFunctor.{max u v, v}.obj ((FrameHom.rightFrameHom r X).obj Y))
      (pinchedHom (G.app (op ⦋0⦌) (nerveVertex (modelRelativeObject C X)))
        (G.app (op ⦋0⦌) (nerveVertex (modelRelativeObject C Y)))) :=
  FrameHom.rightFrameSpecifiedPinchedEquivalence ((modelSourceFrameFamily (C := C)).atObject X)
    r (MorphismProperty.functorialFactorizationData _ _) G hG hH K e Y

end SerrePositivity.EInfinity.SimplicialLocalization
