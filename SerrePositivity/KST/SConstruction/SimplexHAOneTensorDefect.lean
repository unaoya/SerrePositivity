module
public import SerrePositivity.KST.SConstruction.SimplexHAOneTensorRestriction
public import SerrePositivity.KST.SConstruction.SimplexHADegreeDefect

/-! # 元の内部一面での実微分可換性
概要：左右の実復元鎖射があれば、元の内部一面への微分合成の差の制限は零。
方針：元の一面制限の実 tensor 合成表示と、同じ実合成鎖射の微分可換性を使う。
規約：左右の実鎖射の回収条件を保持。使われ方：全次元の逆 Hom 鎖射の次元帰納。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

private lemma differential_difference_factor_zero {V : Type*} [Category V] [Preadditive V]
    {X₀ X₁ Y₀ Y₁ Z₀ Z₁ : V} (f₀ : X₀ ⟶ Y₀) (f₁ : X₁ ⟶ Y₁)
    (dX : X₀ ⟶ X₁) (dY : Y₀ ⟶ Y₁) (dZ : Z₀ ⟶ Z₁)
    (L₀ : Y₀ ⟶ Z₀) (L₁ : Y₁ ⟶ Z₁) (K₀ : X₀ ⟶ Z₀) (K₁ : X₁ ⟶ Z₁)
    (hf : f₀ ≫ dY = dX ≫ f₁) (h₀ : f₀ ≫ L₀ = K₀) (h₁ : f₁ ≫ L₁ = K₁)
    (hK : K₀ ≫ dZ = dX ≫ K₁) : f₀ ≫ (L₀ ≫ dZ - dY ≫ L₁) = 0 := by
  rw [Preadditive.comp_sub, ← Category.assoc f₀ L₀, h₀,
    ← Category.assoc f₀ dY, hf, Category.assoc dX f₁, h₁]
  exact sub_eq_zero.mpr hK

/-- 左右の実復元鎖射があれば、元の内部一面での実微分可換性の差は零。 -/
lemma simplexHADegreeDefect_one_tensor_zero {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D N)
    (n m : ℕ) (v : Fin (n + 1 + m + 1) ↪o Fin (N + 1)) (b : Fin (N + 1))
    (hb : v (Fin.last (n + 1 + m)) < b)
    (F : serreCubeComplex A n ⟶ homObject A D (s.obj (v 0)) (s.obj (simplexHASplitCut n m v)))
    (G : serreCubeComplex A m ⟶ homObject A D (s.obj (simplexHASplitCut n m v)) (s.obj b))
    (hF : ∀ k, F.f k = simplexHADegreeLift A s n (simplexHASplitLeft n m v)
      (simplexHASplitCut n m v) (simplexHASplitLeft_last_lt n m v) k)
    (hG : ∀ k, G.f k = simplexHADegreeLift A s m (simplexHASplitRight n m v) b
      (lt_of_eq_of_lt (simplexHASplitRight_last n m v) hb) k) (k : ℤ) :
    (serreCubeRightFace A true n m).hom.f k ≫
      simplexHADegreeDefect A s (n + 1 + m) v b hb k = 0 := by
  let K := serreCubeTensorComposition A n m F G
  exact differential_difference_factor_zero ((serreCubeRightFace A true n m).hom.f k)
    ((serreCubeRightFace A true n m).hom.f (k + 1))
    ((serreCubeComplex A (n + m)).d k (k + 1))
    ((serreCubeComplex A (n + 1 + m)).d k (k + 1))
    ((homObject A D (s.obj (v 0)) (s.obj b)).d k (k + 1))
    (simplexHADegreeLift A s (n + 1 + m) v b hb k)
    (simplexHADegreeLift A s (n + 1 + m) v b hb (k + 1)) (K.f k) (K.f (k + 1))
    ((serreCubeRightFace A true n m).hom.comm k (k + 1))
    (simplexHADegreeLift_one_tensor_restriction A s n m v b hb F G hF hG k)
    (simplexHADegreeLift_one_tensor_restriction A s n m v b hb F G hF hG (k + 1)) (K.comm k (k + 1))

end SerrePositivity.KST.SConstruction
