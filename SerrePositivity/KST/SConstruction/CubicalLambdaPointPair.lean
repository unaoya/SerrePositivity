module
public import SerrePositivity.KST.SConstruction.CubicalLambdaFunctorPairCoherence
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.LayerTriangles
public import SerrePositivity.DifferentialGraded.Category.TensorInclusions

/-! # Λ 対角による組と元の固定対象の単位挿入
概要：右出力が元の増大と固定対象の閉単位なら、対角による組は元の tensor 包含に等しい。
方針：右増大則を元の任意出力で評価し、同じ右単位逆射と閉単位を挿入する。
規約：固定対象の全 Hom 単位を保持。使われ方：native Perf 作用の固定入力の回収。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Simplicial SSet
open SerrePositivity.DifferentialGraded
open scoped ComonObj

/-- 元の対角の右出力を増大と閉単位にすると、右単位からの同じ単位挿入を回収する。 -/
lemma comonoidFunctorPair_right_point {C : Type z} [Category C] [MonoidalCategory C]
    (P : Comon C) {X Y : C} (f : P.X ⟶ X) (b : 𝟙_ C ⟶ Y) :
    Δ[P.X] ≫ (f ⊗ₘ (ε[P.X] ≫ b)) = f ≫ (ρ_ X).inv ≫ (𝟙 X ⊗ₘ b) := by
  have h : (f ⊗ₘ (ε[P.X] ≫ b)) = (f ⊗ₘ ε[P.X]) ≫ (𝟙 X ⊗ₘ b) := by
    rw [tensorHom_comp_tensorHom, Category.comp_id]
  have hr := congrArg (fun k => k ≫ (ρ_ X).inv) (comonoidFunctorPair_right_unit P f)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hr
  rw [h, ← Category.assoc, hr, Category.assoc]

variable (A : Type u) [CommRing A] {C : Type v} {B : Type w}
  [DGCategory A C] [DGCategory A B]

/-- 元の増大から選ぶ固定右対象との組は、元の同じ tensor 包含の後合成に等しい。 -/
lemma cubicalLambdaFunctorPair_point_right {K : SSet.{u}}
    (F : DGFunctor A (CubicalLambda A K) C) (b : B) :
    cubicalLambdaFunctorPair A F
        (DGFunctor.comp (cubicalLambdaCounit A K) (DGQuotient.pointDGFunctor A B b)) =
      DGFunctor.comp F (dgTensorIncludeFirst A C B b) := by
  refine EnrichedFunctor.ext (Complex A) (fun _ => rfl) ?_
  intro x y
  apply (Category.comp_id _).trans
  change Δ[x ⟶[Complex A] y] ≫ (F.map x y ⊗ₘ (ε[x ⟶[Complex A] y] ≫ eId (Complex A) b)) =
    F.map x y ≫ freeUnitInsert A b (F.obj x ⟶[Complex A] F.obj y)
  exact comonoidFunctorPair_right_point (cubicalLambdaHomComonoid A K x y) (F.map x y)
    (eId (Complex A) b)

end SerrePositivity.KST.SConstruction
