module
public import SerrePositivity.InfinityCategories.Derived.SourceTriangleComponents
public import SerrePositivity.InfinityCategories.Derived.CofiberFiberLiftEquivalence
public import SerrePositivity.InfinityCategories.DGNerve.ComplexTriangleComponents

/-! # 標準 cofiber から標準 fiber 錐への比較三単体

概要：二脚とホモトピーを保つ比較射から上下の比較三単体を作る。
方針：標準 fiber 三角形に前合成し、元の cofiber 三角形との一致を検証する。
規約：全複体の dg nerve 上で構成。使われ方：D7 の錐比較辺の貼合せ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve CochainComplex HomComplex
variable {S : Type u} [CommRing S] {A B C : Complex S}
/-- 下三角形を明示的比較で前合成すると元の cofiber 下三角形になる。 -/
lemma cofiberFiberLower_precompose (f : A ⟶ B) (g : A ⟶ C) :
    SourcePrecomposition.simplex
      (fiberLowerTriangle (pushoutInclusionB f g) (pushoutInclusionC f g)).simplex
      ⟨Cochain.ofHom (cofiberFiberLift f g), δ_ofHom _⟩ =
    (cofiberLowerTriangle f g).simplex := by
  apply dgSimplex2_ext
  · funext i; fin_cases i <;> rfl
  · apply heq_of_eq
    calc
      _ = compose (D := Complex S) S (Cochain.ofHom (pullbackProjectionB (pushoutInclusionB f g)
          (pushoutInclusionC f g))) (Cochain.ofHom (cofiberFiberLift f g)) (zero_add 0) :=
        sourceTriangle_edge01 _ _
      _ = _ := by
        rw [Checks.complex_compose, ← Cochain.ofHom_comp, cofiberFiberLift_projectionB]
        rfl
  · rfl
  · apply heq_of_eq
    calc
      _ = compose (D := Complex S) S (Cochain.ofHom (pullbackDiagonal (pushoutInclusionB f g)
          (pushoutInclusionC f g))) (Cochain.ofHom (cofiberFiberLift f g)) (zero_add 0) :=
        sourceTriangle_edge02 _ _
      _ = _ := by
        rw [Checks.complex_compose, ← Cochain.ofHom_comp, cofiberFiberLift_diagonal]
        rfl
  · apply heq_of_eq
    calc
      _ = compose (D := Complex S) S (fiberNullHomotopy (fiberDifference (pushoutInclusionB f g)
          (pushoutInclusionC f g))) (Cochain.ofHom (cofiberFiberLift f g)) (zero_add (-1)) :=
        sourceTriangle_triple _ _
      _ = _ := by
        rw [Checks.complex_compose]
        exact cofiberFiberLift_homotopy f g

/-- 上三角形を明示的比較で前合成すると元の cofiber 上三角形になる。 -/
lemma cofiberFiberUpper_precompose (f : A ⟶ B) (g : A ⟶ C) :
    SourcePrecomposition.simplex
      (fiberUpperTriangle (pushoutInclusionB f g) (pushoutInclusionC f g)).simplex
      ⟨Cochain.ofHom (cofiberFiberLift f g), δ_ofHom _⟩ =
    (cofiberUpperTriangle f g).simplex := by
  apply dgSimplex2_ext
  · funext i; fin_cases i <;> rfl
  · apply heq_of_eq
    calc
      _ = compose (D := Complex S) S (Cochain.ofHom (pullbackProjectionC
          (pushoutInclusionB f g) (pushoutInclusionC f g)))
          (Cochain.ofHom (cofiberFiberLift f g)) (zero_add 0) := sourceTriangle_edge01 _ _
      _ = _ := by
        rw [Checks.complex_compose, ← Cochain.ofHom_comp, cofiberFiberLift_projectionC]
        rfl
  · rfl
  · apply heq_of_eq
    calc
      _ = compose (D := Complex S) S (Cochain.ofHom (pullbackDiagonal (pushoutInclusionB f g)
          (pushoutInclusionC f g))) (Cochain.ofHom (cofiberFiberLift f g)) (zero_add 0) :=
        sourceTriangle_edge02 _ _
      _ = _ := by
        rw [Checks.complex_compose, ← Cochain.ofHom_comp, cofiberFiberLift_diagonal]
        rfl
  · apply heq_of_eq
    calc
      _ = compose (D := Complex S) S
          (0 : Cochain (pullbackFiber (pushoutInclusionB f g) (pushoutInclusionC f g))
            (pushoutCofiber f g) (-1)) (Cochain.ofHom (cofiberFiberLift f g))
          (zero_add (-1)) := sourceTriangle_triple _ _
      _ = _ := zero_compose _ _

/-- 下側の二つの三角形を結ぶ比較三単体。 -/
def cofiberFiberComparisonLower (f : A ⟶ B) (g : A ⟶ C) : Simplex S (Complex S) 3 :=
  SourcePrecomposition.prepend
    (fiberLowerTriangle (pushoutInclusionB f g) (pushoutInclusionC f g)).simplex
    ⟨Cochain.ofHom (cofiberFiberLift f g), δ_ofHom _⟩

/-- 上側の二つの三角形を結ぶ比較三単体。 -/
def cofiberFiberComparisonUpper (f : A ⟶ B) (g : A ⟶ C) : Simplex S (Complex S) 3 :=
  SourcePrecomposition.prepend
    (fiberUpperTriangle (pushoutInclusionB f g) (pushoutInclusionC f g)).simplex
    ⟨Cochain.ofHom (cofiberFiberLift f g), δ_ofHom _⟩

/-- 下側比較の零面は標準 fiber の下三角形。 -/
lemma cofiberFiberComparisonLower_face_zero (f : A ⟶ B) (g : A ⟶ C) :
    (cofiberFiberComparisonLower f g).pullback (SimplexCategory.δ (0 : Fin 4)).toOrderHom =
      (fiberLowerTriangle (pushoutInclusionB f g) (pushoutInclusionC f g)).simplex :=
  SourcePrecomposition.prepend_face_zero _ _

/-- 下側比較の一面は元の cofiber の下三角形。 -/
lemma cofiberFiberComparisonLower_face_one (f : A ⟶ B) (g : A ⟶ C) :
    (cofiberFiberComparisonLower f g).pullback (SimplexCategory.δ (1 : Fin 4)).toOrderHom =
      (cofiberLowerTriangle f g).simplex :=
  (SourcePrecomposition.prepend_face_one _ _).trans (cofiberFiberLower_precompose f g)

/-- 上側比較の零面は標準 fiber の上三角形。 -/
lemma cofiberFiberComparisonUpper_face_zero (f : A ⟶ B) (g : A ⟶ C) :
    (cofiberFiberComparisonUpper f g).pullback (SimplexCategory.δ (0 : Fin 4)).toOrderHom =
      (fiberUpperTriangle (pushoutInclusionB f g) (pushoutInclusionC f g)).simplex :=
  SourcePrecomposition.prepend_face_zero _ _

/-- 上側比較の一面は元の cofiber の上三角形。 -/
lemma cofiberFiberComparisonUpper_face_one (f : A ⟶ B) (g : A ⟶ C) :
    (cofiberFiberComparisonUpper f g).pullback (SimplexCategory.δ (1 : Fin 4)).toOrderHom =
      (cofiberUpperTriangle f g).simplex :=
  (SourcePrecomposition.prepend_face_one _ _).trans (cofiberFiberUpper_precompose f g)

/-- 比較三単体は始域・fiber・cofiber の共通三角形で一致する。 -/
lemma cofiberFiberComparison_common (f : A ⟶ B) (g : A ⟶ C) :
    (cofiberFiberComparisonLower f g).pullback (SimplexCategory.δ (2 : Fin 4)).toOrderHom =
      (cofiberFiberComparisonUpper f g).pullback (SimplexCategory.δ (2 : Fin 4)).toOrderHom := by
  have hd :
      (fiberLowerTriangle (pushoutInclusionB f g) (pushoutInclusionC f g)).simplex.pullback
        (SimplexCategory.δ (1 : Fin 3)).toOrderHom =
      (fiberUpperTriangle (pushoutInclusionB f g) (pushoutInclusionC f g)).simplex.pullback
        (SimplexCategory.δ (1 : Fin 3)).toOrderHom :=
    (fiberLowerTriangle _ _).d₁.trans (fiberUpperTriangle _ _).d₁.symm
  calc
    _ = SourcePrecomposition.prepend
        ((fiberLowerTriangle (pushoutInclusionB f g) (pushoutInclusionC f g)).simplex.pullback
          (SimplexCategory.δ (1 : Fin 3)).toOrderHom)
        ⟨Cochain.ofHom (cofiberFiberLift f g), δ_ofHom _⟩ := prepend_triangle_face_two _ _
    _ = SourcePrecomposition.prepend
        ((fiberUpperTriangle (pushoutInclusionB f g) (pushoutInclusionC f g)).simplex.pullback
          (SimplexCategory.δ (1 : Fin 3)).toOrderHom)
        ⟨Cochain.ofHom (cofiberFiberLift f g), δ_ofHom _⟩ :=
      prepend_congr hd (heq_of_eq rfl)
    _ = _ := (prepend_triangle_face_two _ _).symm

end SerrePositivity.InfinityCategories
