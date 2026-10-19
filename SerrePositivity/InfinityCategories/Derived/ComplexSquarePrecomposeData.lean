module
public import SerrePositivity.InfinityCategories.Derived.ComplexSquareData
public import SerrePositivity.InfinityCategories.Derived.ComplexTrianglePrecomposition

/-! # 複体の四角形の始点への前合成

概要：始点への鎖写像を四角形の二つの初辺とホモトピーへ前合成する。
方針：三角形の明示的な前合成の式を上下に適用する。
規約：後半二辺を保持する。使われ方：D7 の suspension 比較の中央四角形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.ComplexSquareData
open CategoryTheory DifferentialGraded DGNerve CochainComplex HomComplex
variable {S : Type u} [CommRing S] {V A B C D : Complex S}
variable (s : ComplexSquareData A B C D) (p : V ⟶ A)

/-- 始点の鎖写像を四角形に前合成する。 -/
def precompose : ComplexSquareData V B C D where
  bottom := p ≫ s.bottom
  left := p ≫ s.left
  right := s.right
  top := s.top
  diagonal := p ≫ s.diagonal
  lowerHomotopy := (Cochain.ofHom p).comp s.lowerHomotopy (zero_add (-1))
  upperHomotopy := (Cochain.ofHom p).comp s.upperHomotopy (zero_add (-1))
  lowerEquation := complexTriangle_precompose_differential _ _ _ _ s.lowerEquation p
  upperEquation := complexTriangle_precompose_differential _ _ _ _ s.upperEquation p

/-- 下三角形の前合成との一致。 -/
lemma precompose_lower :
    SourcePrecomposition.simplex s.lowerTriangle ⟨Cochain.ofHom p, δ_ofHom p⟩ =
      (s.precompose p).lowerTriangle :=
  sourcePrecomposition_complexTriangle _ _ _ _ _ _

/-- 上三角形の前合成との一致。 -/
lemma precompose_upper :
    SourcePrecomposition.simplex s.upperTriangle ⟨Cochain.ofHom p, δ_ofHom p⟩ =
      (s.precompose p).upperTriangle :=
  sourcePrecomposition_complexTriangle _ _ _ _ _ _

/-- 下側の前合成比較三単体。 -/
def precomposeLower : Simplex S (Complex S) 3 :=
  SourcePrecomposition.prepend s.lowerTriangle ⟨Cochain.ofHom p, δ_ofHom p⟩

/-- 上側の前合成比較三単体。 -/
def precomposeUpper : Simplex S (Complex S) 3 :=
  SourcePrecomposition.prepend s.upperTriangle ⟨Cochain.ofHom p, δ_ofHom p⟩

/-- 下側比較の零面は元の下三角形。 -/
lemma precomposeLower_face_zero :
    (s.precomposeLower p).pullback (SimplexCategory.δ (0 : Fin 4)).toOrderHom = s.lowerTriangle :=
  SourcePrecomposition.prepend_face_zero _ _

/-- 上側比較の零面は元の上三角形。 -/
lemma precomposeUpper_face_zero :
    (s.precomposeUpper p).pullback (SimplexCategory.δ (0 : Fin 4)).toOrderHom = s.upperTriangle :=
  SourcePrecomposition.prepend_face_zero _ _

/-- 下側比較の一面は前合成した下三角形。 -/
lemma precomposeLower_face_one :
    (s.precomposeLower p).pullback (SimplexCategory.δ (1 : Fin 4)).toOrderHom =
      (s.precompose p).lowerTriangle :=
  (SourcePrecomposition.prepend_face_one _ _).trans (s.precompose_lower p)

/-- 上側比較の一面は前合成した上三角形。 -/
lemma precomposeUpper_face_one :
    (s.precomposeUpper p).pullback (SimplexCategory.δ (1 : Fin 4)).toOrderHom =
      (s.precompose p).upperTriangle :=
  (SourcePrecomposition.prepend_face_one _ _).trans (s.precompose_upper p)

/-- 二比較三単体は対角の二面で一致する。 -/
lemma precompose_common :
    (s.precomposeLower p).pullback (SimplexCategory.δ (2 : Fin 4)).toOrderHom =
      (s.precomposeUpper p).pullback (SimplexCategory.δ (2 : Fin 4)).toOrderHom := by
  unfold precomposeLower precomposeUpper
  rw [prepend_triangle_face_two, prepend_triangle_face_two]
  have h := (complexCompStruct s.bottom s.right s.diagonal s.lowerHomotopy
    s.lowerEquation).d₁.trans
    (complexCompStruct s.left s.top s.diagonal s.upperHomotopy s.upperEquation).d₁.symm
  exact prepend_congr h (heq_of_eq rfl)

end SerrePositivity.InfinityCategories.ComplexSquareData
