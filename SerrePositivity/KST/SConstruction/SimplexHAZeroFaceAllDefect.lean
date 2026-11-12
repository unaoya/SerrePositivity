module
public import SerrePositivity.KST.SConstruction.SimplexHAZeroFaceAllRestriction
public import SerrePositivity.KST.SConstruction.SimplexHADegreeDefect

/-! # 元の全座標の零面と微分可換性の差の還元
概要：任意位置の零面に制限した微分可換性の差を、同じ削除列の前段へ戻す。
方針：元の全次数の面制限と実鎖射性を合わせ、元の始点の等号移送を保持する。
規約：任意の HA データを保持。使われ方：右側に辺が残る零端点生成元の帰納。
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

/-- 元の任意座標の零面への微分可換性の差は、同じ削除列の差の始点移送。 -/
lemma simplexHADegreeDefect_zero_face_all {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (m : ℕ) (q : Fin (m + 1)) (v : Fin (m + 2) ↪o Fin (n + 1))
    (b : Fin (n + 1)) (hb : v (Fin.last (m + 1)) < b) (k : ℤ) :
    (serreCubeFace A false m q).hom.f k ≫ simplexHADegreeDefect A s (m + 1) v b hb k =
      simplexHADegreeDefect A s m (simplexHADeleteVertexOrder m q v) b
        ((v.monotone (Fin.le_last _)).trans_lt hb) k ≫
          (eqToHom (congrArg (fun a => homObject A D (s.obj a) (s.obj b))
            (simplexHADeleteVertexOrder_first m q v))).f (k + 1) := by
  let w := simplexHADeleteVertexOrder m q v
  let hw := (v.monotone
    (Fin.le_last ((simplexHAFaceVertex m q).succAbove (Fin.last m)))).trans_lt hb
  let E : homObject A D (s.obj (w 0)) (s.obj b) ⟶ homObject A D (s.obj (v 0)) (s.obj b) :=
    eqToHom (congrArg (fun a => homObject A D (s.obj a) (s.obj b))
      (simplexHADeleteVertexOrder_first m q v))
  exact differential_difference_postrestrict ((serreCubeFace A false m q).hom.f k)
    ((serreCubeFace A false m q).hom.f (k + 1))
    ((serreCubeComplex A m).d k (k + 1)) ((serreCubeComplex A (m + 1)).d k (k + 1))
    ((homObject A D (s.obj (w 0)) (s.obj b)).d k (k + 1))
    ((homObject A D (s.obj (v 0)) (s.obj b)).d k (k + 1)) (E.f k) (E.f (k + 1))
    (simplexHADegreeLift A s m w b hw k) (simplexHADegreeLift A s m w b hw (k + 1))
    (simplexHADegreeLift A s (m + 1) v b hb k) (simplexHADegreeLift A s (m + 1) v b hb (k + 1))
    ((serreCubeFace A false m q).hom.comm k (k + 1)) (E.comm k (k + 1))
    (simplexHADegreeLift_zero_face_all_restriction A s m q v b hb k)
    (simplexHADegreeLift_zero_face_all_restriction A s m q v b hb (k + 1))

/-- 元の任意位置に零端点を挿入した生成元の差は、同じ前段生成元の差の始点移送。 -/
lemma simplexHADegreeDefect_insert_zero {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (m : ℕ) (q : Fin (m + 1)) (i : SerreCubeGeneratorIndex m)
    (v : Fin (m + 2) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last (m + 1)) < b) (k : ℤ) (hi : serreCubeGeneratorDegree m i = k) :
    simplexHADegreeDefect A s (m + 1) v b hb k
      (eqToHom (congrArg (fun d => (serreCubeComplex A (m + 1)).X d)
        ((serreCubeInsertGeneratorIndex_degree false m q i).trans hi))
        (serreCubeGenerator A (m + 1) (serreCubeInsertGeneratorIndex false m q i))) =
      (eqToHom (congrArg (fun a => homObject A D (s.obj a) (s.obj b))
        (simplexHADeleteVertexOrder_first m q v))).f (k + 1)
          (simplexHADegreeDefect A s m (simplexHADeleteVertexOrder m q v) b
            ((v.monotone (Fin.le_last _)).trans_lt hb) k
            (eqToHom (congrArg (fun d => (serreCubeComplex A m).X d) hi)
              (serreCubeGenerator A m i))) := by
  have h := ConcreteCategory.congr_hom (simplexHADegreeDefect_zero_face_all A s m q v b hb k)
    (eqToHom (congrArg (fun d => (serreCubeComplex A m).X d) hi) (serreCubeGenerator A m i))
  have ht := congrArg (fun x => simplexHADegreeDefect A s (m + 1) v b hb k x)
    (serreCubeFace_generator_cast A false m q i k hi)
  exact ht.symm.trans h

end SerrePositivity.KST.SConstruction
