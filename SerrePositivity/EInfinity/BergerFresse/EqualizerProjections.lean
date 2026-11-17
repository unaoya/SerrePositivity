module

public import SerrePositivity.EInfinity.BergerFresse.EqualizerFunctor

/-!
# 同じBF等化子の元の射影と整合性

Berger–Fresse §2.2・§3.1、M14 L23、報告 §416。
元の等化子包含と元の全積の射影を合成し、同じ単体射の前後合成で読む。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BergerFresse
open CategoryTheory Limits
open SerrePositivity.Cosimplicial (CosimplicialAlgebra)
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 元の全積への等化子包含から得る同じq成分（BF §3.1）。 -/
def bfProjection (X : CosimplicialAlgebra A) (q : ℕ) :
    bfNormalizedObj A X ⟶ (convolutionAt A q q).obj X :=
  equalizer.ι ((post A).app X) ((pre A).app X) ≫
    (convolutionProductProjection A q).app X

/-- 元の等化子条件を同じ単体射の成分で読む（BF §3.1）。 -/
lemma bfProjection_compatible (X : CosimplicialAlgebra A)
    {q r : ℕ} (α : (⦋q⦌ : SimplexCategory) ⟶ ⦋r⦌) :
    bfProjection A X q ≫ (postAt A α).app X =
      bfProjection A X r ≫ (preAt A α).app X := by
  have h := congrArg (fun f => f ≫
    Pi.π (fun i : SimplexMorphismIndex => (convolutionAt A i.1 i.2.1).obj X)
      ⟨q, r, α⟩) (equalizer.condition ((post A).app X) ((pre A).app X))
  simpa only [post, pre, convolutionProductLift, NatTrans.comp_app, Category.assoc,
    Pi.lift_comp_π, bfProjection] using h

/-- 同じ等化子の射影は全余単体的射に自然（BF §3.1）。 -/
lemma bfProjection_naturality {X Y : CosimplicialAlgebra A} (f : X ⟶ Y) (q : ℕ) :
    bfNormalizedMap A f ≫ bfProjection A Y q =
      bfProjection A X q ≫ (convolutionAt A q q).map f := by
  unfold bfProjection bfNormalizedMap
  rw [← Category.assoc, equalizer.lift_ι]
  rw [Category.assoc, (convolutionProductProjection A q).naturality f]
  exact (Category.assoc _ _ _).symm

end SerrePositivity.EInfinity.BergerFresse
