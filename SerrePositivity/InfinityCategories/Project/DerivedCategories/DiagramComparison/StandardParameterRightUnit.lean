module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StandardParameterAugmentationValues
public import SerrePositivity.EInfinity.BarrattEccles.Unitors
/-!
概要：零次標準単体の増大写像と右単位子の値を合成する。
方針：零次数へ代入して、既存の二つの値公式を使う。
規約：A05aの最後の切断の証明の分割。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory HomologicalComplex AlgebraicTopology AlgebraicTopology.DoldKan
open SerrePositivity.EInfinity.ComplexLimits
open scoped Simplicial TensorProduct
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
/-- 零鎖次数の標準単体増大写像を通すと右単位子は元の値を返す。 -/
theorem standardParameter_right_unit (A : Type u) [CommRing A]
    (n : SimplexCategory) (P : CochainComplex (ModuleCat A) ℤ)
    (r : ℕ) (hr : r = 0) (q : ℤ)
    (a : ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n)).obj (Opposite.op ⦋r⦌))
    (x : P.X q) :
    let W := (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n) ⋙ ModuleCat.free A
    (ρ_ P).hom.f q (ιTensorObj P (𝟙_ (CochainComplex (ModuleCat A) ℤ)) q (-(r : ℤ)) q
      (by subst r; simp) (x ⊗ₜ[A]
      (normalizedSimplexCochainContraction A n).hom.f (-(r : ℤ))
        ((((normalizedMooreComplex (ModuleCat A)).obj W).extendXIso
          ComplexShape.embeddingDownNat (i := r) (i' := -(r : ℤ)) rfl).inv
          ((PInftyToNormalizedMooreComplex W).f r (ModuleCat.freeMk a))))) = x := by
  subst r
  dsimp only [Int.natCast_zero, neg_zero]
  erw [standardParameterAugmentation_moore_generator]
  simp only [neg_zero]
  erw [← SerrePositivity.EInfinity.BarrattEccles.cochain_rightUnitor_inv_apply]
  exact ConcreteCategory.congr_hom
    (congrArg (fun f => f.f q) (ρ_ P).inv_hom_id) x
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
