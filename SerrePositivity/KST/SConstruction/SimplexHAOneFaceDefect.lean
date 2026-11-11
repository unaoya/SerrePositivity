module
public import SerrePositivity.KST.SConstruction.SimplexHADegreeDefect
public import SerrePositivity.KST.SConstruction.SimplexHAOneFaceRestriction

/-! # 元の一端点追加と微分可換性の差の還元
概要：右端一面に制限した微分可換性の差は、前段の差と元の閉零辺との実右合成。
方針：元の両面次数制限と、元の面射・右合成射の鎖射性を加法圏の合成則で合わせる。
規約：元の辺・次数・生成元を保持。使われ方：混在生成元の一端点追加の帰納。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

private lemma differential_difference_postrestrict {V : Type*} [Category V] [Preadditive V]
    {X₀ X₁ Y₀ Y₁ K₀ K₁ L₀ L₁ : V} (f₀ : X₀ ⟶ Y₀) (f₁ : X₁ ⟶ Y₁)
    (dX : X₀ ⟶ X₁) (dY : Y₀ ⟶ Y₁) (dK : K₀ ⟶ K₁) (dL : L₀ ⟶ L₁)
    (r₀ : K₀ ⟶ L₀) (r₁ : K₁ ⟶ L₁) (U₀ : X₀ ⟶ K₀) (U₁ : X₁ ⟶ K₁)
    (M₀ : Y₀ ⟶ L₀) (M₁ : Y₁ ⟶ L₁)
    (hf : f₀ ≫ dY = dX ≫ f₁) (hr : r₀ ≫ dL = dK ≫ r₁)
    (h₀ : f₀ ≫ M₀ = U₀ ≫ r₀) (h₁ : f₁ ≫ M₁ = U₁ ≫ r₁) :
    f₀ ≫ (M₀ ≫ dL - dY ≫ M₁) = (U₀ ≫ dK - dX ≫ U₁) ≫ r₁ := by
  rw [Preadditive.comp_sub, Preadditive.sub_comp, ← Category.assoc f₀ M₀, h₀,
    Category.assoc U₀ r₀, hr, ← Category.assoc U₀ dK,
    ← Category.assoc f₀ dY, hf, Category.assoc dX f₁, h₁, ← Category.assoc dX U₁]

/-- 元の右端一面への制限の微分可換性の差は、前段の差と元の閉零辺との実右合成。 -/
lemma simplexHADegreeDefect_one_face {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n)
    (m : ℕ) (v : Fin (m + 2) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last (m + 1)) < b) (k : ℤ) :
    (serreCubeFace A true m 0).hom.f k ≫
        simplexHADegreeDefect A s.toSimplexData (m + 1) v b hb k =
      simplexHADegreeDefect A s.toSimplexData m (Fin.castSuccOrderEmb.trans v)
        (v (Fin.last (m + 1))) (simplexHADecodePrefix_last m v) k ≫
        (dgRightCycleComposition A (x := s.obj (v 0))
          (s.edgeCycle (v (Fin.last (m + 1))) b hb)).f (k + 1) := by
  let r := v (Fin.last (m + 1))
  let R := dgRightCycleComposition A (x := s.obj (v 0)) (s.edgeCycle r b hb)
  exact differential_difference_postrestrict ((serreCubeFace A true m 0).hom.f k)
    ((serreCubeFace A true m 0).hom.f (k + 1))
    ((serreCubeComplex A m).d k (k + 1)) ((serreCubeComplex A (m + 1)).d k (k + 1))
    ((homObject A D (s.obj (v 0)) (s.obj r)).d k (k + 1))
    ((homObject A D (s.obj (v 0)) (s.obj b)).d k (k + 1)) (R.f k) (R.f (k + 1))
    (simplexHADegreeLift A s.toSimplexData m (Fin.castSuccOrderEmb.trans v) r
      (simplexHADecodePrefix_last m v) k)
    (simplexHADegreeLift A s.toSimplexData m (Fin.castSuccOrderEmb.trans v) r
      (simplexHADecodePrefix_last m v) (k + 1))
    (simplexHADegreeLift A s.toSimplexData (m + 1) v b hb k)
    (simplexHADegreeLift A s.toSimplexData (m + 1) v b hb (k + 1))
    ((serreCubeFace A true m 0).hom.comm k (k + 1)) (R.comm k (k + 1))
    (simplexHADegreeLift_one_face_restriction A s m v b hb k)
    (simplexHADegreeLift_one_face_restriction A s m v b hb (k + 1))

/-- 元の一端点追加生成元の微分可換性の差は、前段の同じ差と元の閉零辺との右合成。 -/
lemma simplexHADegreeDefect_point_one {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n)
    (m : ℕ) (i : SerreCubeGeneratorIndex m) (v : Fin (m + 2) ↪o Fin (n + 1))
    (b : Fin (n + 1)) (hb : v (Fin.last (m + 1)) < b) (k : ℤ)
    (hi : serreCubeGeneratorDegree m i = k) :
    simplexHADegreeDefect A s.toSimplexData (m + 1) v b hb k
        (eqToHom (congrArg (fun d => (serreCubeComplex A (m + 1)).X d)
          (show serreCubeGeneratorDegree (m + 1) (i, 1) = k from (add_zero _).trans hi))
          (serreCubeGenerator A (m + 1) (i, 1))) =
      (dgRightCycleComposition A (x := s.obj (v 0))
        (s.edgeCycle (v (Fin.last (m + 1))) b hb)).f (k + 1)
        (simplexHADegreeDefect A s.toSimplexData m (Fin.castSuccOrderEmb.trans v)
          (v (Fin.last (m + 1))) (simplexHADecodePrefix_last m v) k
          (eqToHom (congrArg (fun d => (serreCubeComplex A m).X d) hi)
            (serreCubeGenerator A m i))) := by
  have h := ConcreteCategory.congr_hom (simplexHADegreeDefect_one_face A s m v b hb k)
    (eqToHom (congrArg (fun d => (serreCubeComplex A m).X d) hi) (serreCubeGenerator A m i))
  have ht := congrArg (fun w => simplexHADegreeDefect A s.toSimplexData (m + 1) v b hb k w)
    (serreCubeGenerator_point_cast A true m i k hi)
  exact ht.symm.trans h

end SerrePositivity.KST.SConstruction
