module
public import SerrePositivity.KST.SConstruction.DGNativePointSimplex

/-! # native tensor の左定数因子と元の単位挿入
概要：ラベルを左に固定した元の native tensor 比較を、同じ dg tensor 包含へ戻す。
方針：左増大則と単位の braiding を使い、非対称な Serre 対角の順序を保つ。
規約：tensor 比較の対称性は仮定しない。使われ方：native Perf 作用の入力辺の成分評価。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped ComonObj

/-- 左増大と同じ閉単位を使うと、元の左単位からの挿入を回収する。 -/
lemma comonoidFunctorPair_left_point {C : Type z} [Category C] [MonoidalCategory C]
    (P : Comon C) {X Y : C} (b : 𝟙_ C ⟶ X) (f : P.X ⟶ Y) :
    Δ[P.X] ≫ ((ε[P.X] ≫ b) ⊗ₘ f) = f ≫ (λ_ Y).inv ≫ (b ⊗ₘ 𝟙 Y) := by
  have h : ((ε[P.X] ≫ b) ⊗ₘ f) = (ε[P.X] ⊗ₘ f) ≫ (b ⊗ₘ 𝟙 Y) := by
    rw [tensorHom_comp_tensorHom, Category.comp_id]
  have hl := congrArg (fun k => k ≫ (λ_ Y).inv) (comonoidFunctorPair_left_unit P f)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hl
  rw [h, ← Category.assoc, hl, Category.assoc]

/-- 同じ左単位挿入を、元の dg 第二包含で用いる右単位と braiding で表す。 -/
lemma comonoidFunctorPair_left_point_braided
    {C : Type z} [Category C] [MonoidalCategory C] [BraidedCategory C]
    (P : Comon C) {X Y : C} (b : 𝟙_ C ⟶ X) (f : P.X ⟶ Y) :
    Δ[P.X] ≫ ((ε[P.X] ≫ b) ⊗ₘ f) =
      f ≫ (ρ_ Y).inv ≫ (𝟙 Y ⊗ₘ b) ≫ (β_ Y X).hom := by
  rw [comonoidFunctorPair_left_point, BraidedCategory.braiding_naturality (𝟙 Y) b,
    ← Category.assoc (ρ_ Y).inv, rightUnitor_inv_braiding]

variable (R : Type u) [CommRing R] {C : Type v} {B : Type w}
  [DGCategory R C] [DGCategory R B]

/-- 同じ左定数対象との Λ の組は、元の dg 第二包含への後合成そのもの。 -/
lemma cubicalLambdaFunctorPair_point_left {K : SSet.{u}} (b : B)
    (F : DGFunctor R (CubicalLambda R K) C) :
    cubicalLambdaFunctorPair R
        (DGFunctor.comp (cubicalLambdaCounit R K) (DGQuotient.pointDGFunctor R B b)) F =
      DGFunctor.comp F (dgTensorIncludeSecond R B C b) := by
  refine EnrichedFunctor.ext (Complex R) (fun _ => rfl) ?_
  intro x y
  apply (Category.comp_id _).trans
  change Δ[x ⟶[Complex R] y] ≫ ((ε[x ⟶[Complex R] y] ≫ eId (Complex R) b) ⊗ₘ
    F.map x y) = F.map x y ≫ dgTensorSecondHom R B C b (F.obj x) (F.obj y)
  erw [comonoidFunctorPair_left_point_braided (cubicalLambdaHomComonoid R K x y)
    (eId (Complex R) b) (F.map x y)]
  simp only [dgTensorSecondHom, freeUnitInsert, Category.assoc, braiding_eq_existing, signedSwap]
  rfl

/-- 左因子を同じ対象に固定した全 native tensor 単体は、元の dg 包含の像。 -/
lemma dgNerveTensorSimplex_point_left {N : ℕ} (b : B) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C N) :
    dgNerveTensorSimplex R (dgNativePointSimplex R B b N) t =
      t.map (dgTensorIncludeSecond R B C b) := by
  unfold dgNerveTensorSimplex dgNativePointSimplex
  rw [simplexHAInverseFunctor_native, cubicalLambdaFunctorPair_point_left,
    cubicalLambdaNativeSimplex_post, cubicalLambdaNativeSimplex_inverse]

end SerrePositivity.KST.SConstruction
