module
public import SerrePositivity.KST.SConstruction.SimplexHAZeroFaceRestriction

/-! # 元の HA 線形復元の微分可換性の差
概要：元の二つの実微分との合成の差を作り、右端零面への制限を前段の同じ差へ戻す。
方針：元の全次数の零面制限と、元の面射の鎖射性を一般の加法圏の合成則で合わせる。
規約：任意の HA データと実微分を保持。使われ方：零端点追加生成元の微分条件の帰納。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の HA 線形復元と、元の始域・終域微分の二つの合成の差。 -/
def simplexHADegreeDefect {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n) (m : ℕ)
    (v : Fin (m + 1) ↪o Fin (n + 1)) (b : Fin (n + 1)) (hb : v (Fin.last m) < b) (k : ℤ) :
    (serreCubeComplex A m).X k ⟶ (homObject A D (s.obj (v 0)) (s.obj b)).X (k + 1) :=
  simplexHADegreeLift A s m v b hb k ≫ (homObject A D (s.obj (v 0)) (s.obj b)).d k (k + 1) -
    (serreCubeComplex A m).d k (k + 1) ≫ simplexHADegreeLift A s m v b hb (k + 1)

private lemma differential_difference_restrict {V : Type*} [Category V] [Preadditive V]
    {X₀ X₁ Y₀ Y₁ K₀ K₁ : V} (f₀ : X₀ ⟶ Y₀) (f₁ : X₁ ⟶ Y₁)
    (dX : X₀ ⟶ X₁) (dY : Y₀ ⟶ Y₁) (dK : K₀ ⟶ K₁)
    (L₀ : X₀ ⟶ K₀) (L₁ : X₁ ⟶ K₁) (M₀ : Y₀ ⟶ K₀) (M₁ : Y₁ ⟶ K₁)
    (hf : f₀ ≫ dY = dX ≫ f₁) (h₀ : f₀ ≫ M₀ = L₀) (h₁ : f₁ ≫ M₁ = L₁) :
    f₀ ≫ (M₀ ≫ dK - dY ≫ M₁) = L₀ ≫ dK - dX ≫ L₁ := by
  rw [Preadditive.comp_sub, ← Category.assoc f₀ M₀, h₀,
    ← Category.assoc f₀ dY, hf, Category.assoc dX f₁, h₁]

/-- 元の右端零面へ制限した微分可換性の差は、削除頂点列の前段の同じ差。 -/
lemma simplexHADegreeDefect_zero_face {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (m : ℕ) (v : Fin (m + 2) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last (m + 1)) < b) (k : ℤ) :
    (serreCubeFace A false m 0).hom.f k ≫ simplexHADegreeDefect A s (m + 1) v b hb k =
      simplexHADegreeDefect A s m (Fin.castSuccOrderEmb.trans v) b
        ((simplexHADecodePrefix_last m v).trans hb) k :=
  differential_difference_restrict ((serreCubeFace A false m 0).hom.f k)
    ((serreCubeFace A false m 0).hom.f (k + 1))
    ((serreCubeComplex A m).d k (k + 1)) ((serreCubeComplex A (m + 1)).d k (k + 1))
    ((homObject A D (s.obj (v 0)) (s.obj b)).d k (k + 1))
    (simplexHADegreeLift A s m (Fin.castSuccOrderEmb.trans v) b
      ((simplexHADecodePrefix_last m v).trans hb) k)
    (simplexHADegreeLift A s m (Fin.castSuccOrderEmb.trans v) b
      ((simplexHADecodePrefix_last m v).trans hb) (k + 1))
    (simplexHADegreeLift A s (m + 1) v b hb k)
    (simplexHADegreeLift A s (m + 1) v b hb (k + 1))
    ((serreCubeFace A false m 0).hom.comm k (k + 1))
    (simplexHADegreeLift_zero_face_restriction A s m v b hb k)
    (simplexHADegreeLift_zero_face_restriction A s m v b hb (k + 1))

/-- 元の零端点追加生成元の微分可換性の差は、同じ前段の生成元の差を回収する。 -/
lemma simplexHADegreeDefect_point_zero {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (m : ℕ) (i : SerreCubeGeneratorIndex m) (v : Fin (m + 2) ↪o Fin (n + 1))
    (b : Fin (n + 1)) (hb : v (Fin.last (m + 1)) < b) (k : ℤ)
    (hi : serreCubeGeneratorDegree m i = k) :
    simplexHADegreeDefect A s (m + 1) v b hb k
        (eqToHom (congrArg (fun d => (serreCubeComplex A (m + 1)).X d)
          (show serreCubeGeneratorDegree (m + 1) (i, 0) = k from (add_zero _).trans hi))
          (serreCubeGenerator A (m + 1) (i, 0))) =
      simplexHADegreeDefect A s m (Fin.castSuccOrderEmb.trans v) b
        ((simplexHADecodePrefix_last m v).trans hb) k
        (eqToHom (congrArg (fun d => (serreCubeComplex A m).X d) hi)
          (serreCubeGenerator A m i)) := by
  have h := ConcreteCategory.congr_hom (simplexHADegreeDefect_zero_face A s m v b hb k)
    (eqToHom (congrArg (fun d => (serreCubeComplex A m).X d) hi) (serreCubeGenerator A m i))
  have ht := congrArg (fun w => simplexHADegreeDefect A s (m + 1) v b hb k w)
    (serreCubeGenerator_point_cast A false m i k hi)
  exact ht.symm.trans h

end SerrePositivity.KST.SConstruction
