module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedBKFreeTensorRow
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeTensorHomInverseEvaluation

/-!
概要：A09の実tensor逆射にA12の指定Hom比較を入れた成分を実錐代表との合成で計算する。
方針：同じ逆転置成分・A12の全cochain評価・AsSmall制限・BK行のtensor合成則を合わせる。
規約：全標準単体パラメータと任意の自由重みの元を保持する既存構成の評価則。
使われ方：HA 1.2.4、IS-W2 B02のAW各切断の左辺を閉じる指定射の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory MonoidalCategory CochainComplex HomComplex HomologicalComplex AlgebraicTopology
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open scoped TensorProduct
variable {A : Type u} [CommRing A]
local notation "V" => Functor.flip (Functor.obj SimplicialObject.opFunctor bousfieldKanSetWeight)

/-- 同じA12像をA09のtensor逆射へ入れた全斉次tensor成分は元の錐代表との実合成。 -/
theorem reflectedBKFreeTensor_inverse_component (P : Complex A)
    (X : CosimplicialObject (Complex A)) (m : SimplexCategory)
    (α : ((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).obj
      (homComplex A P ((productTotalFunctor A).obj X))).obj (Opposite.op m))
    (n : ℕ) (p r : ℤ) (hr : p - n = r)
    (j : AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ))
    (w : ((freeNegativeChainsDiagram (A := A)
      (reflectedNormalizedBKSmallWeight A)).obj j).X (-(n : ℤ)))
    (x : ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
      (SSet.stdSimplex.obj m)).X p) :
    let Y := (homDiagramFunctor P).obj X
    let γ := homToNormalizedBousfieldKan P X ≫ (normalizedBKReverseHomotopyEquiv Y).hom ≫
      (reflectedNormalizedBKSmallHomIso A Y).hom
    let t := (freeTensorDiagramHomIso A (normalizedBKSmallDiagram A Y)
      (reflectedNormalizedBKSmallWeight A)).inv.app (Opposite.op m)
        (((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map γ).app (Opposite.op m) α)
    let σ := (normalizedLinearWeightDiagramIso A V).inv ≫
      extendMap (normalizedMooreReverse.app (linearizedSimplicialWeight A bousfieldKanSetWeight))
        ComplexShape.embeddingDownNat
    (t.app j).f r (ιTensorObj
      ((freeNegativeChainsDiagram (A := A) (reflectedNormalizedBKSmallWeight A)).obj j)
      ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
        (SSet.stdSimplex.obj m)) (-(n : ℤ)) p r (by omega) (w ⊗ₜ[A] x)) =
      compose A (D := Complex A) (p := p) (q := -(n : ℤ)) (n := r)
        (x := P) (y := (productTotalFunctor A).obj X)
        (z := (doubleOppositeDiagram X).obj (AsSmall.down.obj j))
        ((((σ ≫ normalizedBousfieldKanConeRepresentative X).f (-(n : ℤ))).app
          (AsSmall.down.obj j)) w)
        (((_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A (homComplex A P ((productTotalFunctor A).obj X)) m).symm
          α).f p x) (by omega) := by
  dsimp only
  let Y := (homDiagramFunctor P).obj X
  let W := reflectedNormalizedBKSmallWeight A
  let Q := normalizedBKSmallDiagram A Y
  let γ := homToNormalizedBousfieldKan P X ≫ (normalizedBKReverseHomotopyEquiv Y).hom ≫
    (reflectedNormalizedBKSmallHomIso A Y).hom
  let β := ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A
    (homComplex A P ((productTotalFunctor A).obj X)) m).symm α).f p x
  let σ := (normalizedLinearWeightDiagramIso A V).inv ≫
    extendMap (normalizedMooreReverse.app (linearizedSimplicialWeight A bousfieldKanSetWeight))
      ComplexShape.embeddingDownNat
  have hv := freeTensorDiagramHomIso_inv_map_component A W Q
    (homComplex A P ((productTotalFunctor A).obj X)) γ m α j (-(n : ℤ)) p r
      (by omega) w x
  change _ = ((-(n : ℤ)) * p).negOnePow •
    (((γ.f p β).v (-(n : ℤ)) r (by omega)).app j) w at hv
  have hγ := reflectedNormalizedBKSmallHomIso_reverse_apply A Y p
    ((homToNormalizedBousfieldKan P X).f p β)
  change γ.f p β = _ at hγ
  have hc := congrArg (fun z : Cochain
      ((functorToComplexOfFunctors (AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ))
        (ModuleCat A) (ComplexShape.up ℤ)).obj (freeNegativeChainsDiagram (A := A) W))
      ((functorToComplexOfFunctors (AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ))
        (ModuleCat A) (ComplexShape.up ℤ)).obj Q) p =>
        ((z.v (-(n : ℤ)) r (by omega)).app j) w) hγ
  change (((γ.f p β).v (-(n : ℤ)) r (by omega)).app j) w =
    ((((Cochain.ofHom σ).comp ((homToNormalizedBousfieldKan P X).f p β) (zero_add p)).v
      (-(n : ℤ)) r (by omega)).app (AsSmall.down.obj j)) w at hc
  have hs := congrArg (fun z : Homogeneous P
      ((doubleOppositeDiagram X).obj (AsSmall.down.obj j)) r =>
        ((-(n : ℤ)) * p).negOnePow • z) hc
  have hb := reflectedBKFreeHom_tensor_component_of_degree P X p n r hr β
    (AsSmall.down.obj j) w
  exact hv.trans (hs.trans hb)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
