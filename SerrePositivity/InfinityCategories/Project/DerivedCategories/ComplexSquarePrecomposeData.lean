module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexTrianglePrecomposition

/-! # 複体の四角形の始点への前合成

概要：始点への鎖写像を四角形の二つの初辺とホモトピーへ前合成する。
方針：三角形の明示的な前合成の式を上下に適用する。
規約：後半二辺を保持する。使われ方：D7 の suspension 比較の中央四角形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable {S : Type u} [CommRing S] {V A B C D : _root_.SerrePositivity.DifferentialGraded.Complex S}
variable (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData A B C D) (p : V ⟶ A)

/-- 始点の鎖写像を四角形に前合成する。 -/
def precompose : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData V B C D where
  bottom := p ≫ s.bottom
  left := p ≫ s.left
  right := s.right
  top := s.top
  diagonal := p ≫ s.diagonal
  lowerHomotopy := (Cochain.ofHom p).comp s.lowerHomotopy (zero_add (-1))
  upperHomotopy := (Cochain.ofHom p).comp s.upperHomotopy (zero_add (-1))
  lowerEquation := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangle_precompose_differential _ _ _ _ s.lowerEquation p
  upperEquation := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangle_precompose_differential _ _ _ _ s.upperEquation p

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (precompose)


/-- 下三角形の前合成との一致。 -/
lemma precompose_lower :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.simplex s.lowerTriangle ⟨Cochain.ofHom p, δ_ofHom p⟩ =
      (s.precompose p).lowerTriangle :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sourcePrecomposition_complexTriangle _ _ _ _ _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (precompose_lower)


/-- 上三角形の前合成との一致。 -/
lemma precompose_upper :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.simplex s.upperTriangle ⟨Cochain.ofHom p, δ_ofHom p⟩ =
      (s.precompose p).upperTriangle :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sourcePrecomposition_complexTriangle _ _ _ _ _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (precompose_upper)


/-- 下側の前合成比較三単体。 -/
def precomposeLower : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (Complex S) 3 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend s.lowerTriangle ⟨Cochain.ofHom p, δ_ofHom p⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (precomposeLower)


/-- 上側の前合成比較三単体。 -/
def precomposeUpper : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (Complex S) 3 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend s.upperTriangle ⟨Cochain.ofHom p, δ_ofHom p⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (precomposeUpper)


/-- 下側比較の零面は元の下三角形。 -/
lemma precomposeLower_face_zero :
    (s.precomposeLower p).pullback (SimplexCategory.δ (0 : Fin 4)).toOrderHom = s.lowerTriangle :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend_face_zero _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (precomposeLower_face_zero)


/-- 上側比較の零面は元の上三角形。 -/
lemma precomposeUpper_face_zero :
    (s.precomposeUpper p).pullback (SimplexCategory.δ (0 : Fin 4)).toOrderHom = s.upperTriangle :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend_face_zero _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (precomposeUpper_face_zero)


/-- 下側比較の一面は前合成した下三角形。 -/
lemma precomposeLower_face_one :
    (s.precomposeLower p).pullback (SimplexCategory.δ (1 : Fin 4)).toOrderHom =
      (s.precompose p).lowerTriangle :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend_face_one _ _).trans (s.precompose_lower p)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (precomposeLower_face_one)


/-- 上側比較の一面は前合成した上三角形。 -/
lemma precomposeUpper_face_one :
    (s.precomposeUpper p).pullback (SimplexCategory.δ (1 : Fin 4)).toOrderHom =
      (s.precompose p).upperTriangle :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend_face_one _ _).trans (s.precompose_upper p)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (precomposeUpper_face_one)


/-- 二比較三単体は対角の二面で一致する。 -/
lemma precompose_common :
    (s.precomposeLower p).pullback (SimplexCategory.δ (2 : Fin 4)).toOrderHom =
      (s.precomposeUpper p).pullback (SimplexCategory.δ (2 : Fin 4)).toOrderHom := by
  unfold precomposeLower precomposeUpper
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend_triangle_face_two, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend_triangle_face_two]
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexCompStruct s.bottom s.right s.diagonal s.lowerHomotopy
    s.lowerEquation).d₁.trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexCompStruct s.left s.top s.diagonal s.upperHomotopy s.upperEquation).d₁.symm
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend_congr h (heq_of_eq rfl)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (precompose_common)


end SerrePositivity.InfinityCategories.Project.DerivedCategories
