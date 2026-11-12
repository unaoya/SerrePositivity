module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SourceTriangleComponents
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CofiberFiberLiftEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ComplexTriangleComponents

/-! # 標準 cofiber から標準 fiber 錐への比較三単体

概要：二脚とホモトピーを保つ比較射から上下の比較三単体を作る。
方針：標準 fiber 三角形に前合成し、元の cofiber 三角形との一致を検証する。
規約：全複体の dg nerve 上で構成。使われ方：D7 の錐比較辺の貼合せ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable {S : Type u} [CommRing S] {A B C : _root_.SerrePositivity.DifferentialGraded.Complex S}
/-- 下三角形を明示的比較で前合成すると元の cofiber 下三角形になる。 -/
lemma cofiberFiberLower_precompose (f : A ⟶ B) (g : A ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.simplex
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberLowerTriangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB f g) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionC f g)).simplex
      ⟨Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberLift f g), δ_ofHom _⟩ =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberLowerTriangle f g).simplex := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplex2_ext
  · funext i; fin_cases i <;> rfl
  · apply heq_of_eq
    calc
      _ = compose (D := Complex S) S (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionB (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB f g)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionC f g))) (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberLift f g)) (zero_add 0) :=
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sourceTriangle_edge01 _ _
      _ = _ := by
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.complex_compose, ← Cochain.ofHom_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberLift_projectionB]
        rfl
  · rfl
  · apply heq_of_eq
    calc
      _ = compose (D := Complex S) S (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackDiagonal (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB f g)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionC f g))) (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberLift f g)) (zero_add 0) :=
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sourceTriangle_edge02 _ _
      _ = _ := by
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.complex_compose, ← Cochain.ofHom_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberLift_diagonal]
        rfl
  · apply heq_of_eq
    calc
      _ = compose (D := Complex S) S (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberNullHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberDifference (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB f g)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionC f g))) (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberLift f g)) (zero_add (-1)) :=
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sourceTriangle_triple _ _
      _ = _ := by
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.complex_compose]
        exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberLift_homotopy f g

/-- 上三角形を明示的比較で前合成すると元の cofiber 上三角形になる。 -/
lemma cofiberFiberUpper_precompose (f : A ⟶ B) (g : A ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.simplex
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberUpperTriangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB f g) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionC f g)).simplex
      ⟨Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberLift f g), δ_ofHom _⟩ =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberUpperTriangle f g).simplex := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplex2_ext
  · funext i; fin_cases i <;> rfl
  · apply heq_of_eq
    calc
      _ = compose (D := Complex S) S (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionC
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB f g) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionC f g)))
          (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberLift f g)) (zero_add 0) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sourceTriangle_edge01 _ _
      _ = _ := by
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.complex_compose, ← Cochain.ofHom_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberLift_projectionC]
        rfl
  · rfl
  · apply heq_of_eq
    calc
      _ = compose (D := Complex S) S (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackDiagonal (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB f g)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionC f g))) (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberLift f g)) (zero_add 0) :=
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sourceTriangle_edge02 _ _
      _ = _ := by
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.complex_compose, ← Cochain.ofHom_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberLift_diagonal]
        rfl
  · apply heq_of_eq
    calc
      _ = _root_.SerrePositivity.DifferentialGraded.compose (D := _root_.SerrePositivity.DifferentialGraded.Complex S) S
          (0 : Cochain (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackFiber (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB f g) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionC f g))
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutCofiber f g) (-1)) (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberLift f g))
          (zero_add (-1)) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sourceTriangle_triple _ _
      _ = _ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose _ _

/-- 下側の二つの三角形を結ぶ比較三単体。 -/
def cofiberFiberComparisonLower (f : A ⟶ B) (g : A ⟶ C) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (Complex S) 3 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberLowerTriangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB f g) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionC f g)).simplex
    ⟨Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberLift f g), δ_ofHom _⟩

/-- 上側の二つの三角形を結ぶ比較三単体。 -/
def cofiberFiberComparisonUpper (f : A ⟶ B) (g : A ⟶ C) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (Complex S) 3 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberUpperTriangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB f g) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionC f g)).simplex
    ⟨Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberLift f g), δ_ofHom _⟩

/-- 下側比較の零面は標準 fiber の下三角形。 -/
lemma cofiberFiberComparisonLower_face_zero (f : A ⟶ B) (g : A ⟶ C) :
    (cofiberFiberComparisonLower f g).pullback (SimplexCategory.δ (0 : Fin 4)).toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberLowerTriangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB f g) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionC f g)).simplex :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend_face_zero _ _

/-- 下側比較の一面は元の cofiber の下三角形。 -/
lemma cofiberFiberComparisonLower_face_one (f : A ⟶ B) (g : A ⟶ C) :
    (cofiberFiberComparisonLower f g).pullback (SimplexCategory.δ (1 : Fin 4)).toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberLowerTriangle f g).simplex :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend_face_one _ _).trans (cofiberFiberLower_precompose f g)

/-- 上側比較の零面は標準 fiber の上三角形。 -/
lemma cofiberFiberComparisonUpper_face_zero (f : A ⟶ B) (g : A ⟶ C) :
    (cofiberFiberComparisonUpper f g).pullback (SimplexCategory.δ (0 : Fin 4)).toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberUpperTriangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB f g) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionC f g)).simplex :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend_face_zero _ _

/-- 上側比較の一面は元の cofiber の上三角形。 -/
lemma cofiberFiberComparisonUpper_face_one (f : A ⟶ B) (g : A ⟶ C) :
    (cofiberFiberComparisonUpper f g).pullback (SimplexCategory.δ (1 : Fin 4)).toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberUpperTriangle f g).simplex :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend_face_one _ _).trans (cofiberFiberUpper_precompose f g)

/-- 比較三単体は始域・fiber・cofiber の共通三角形で一致する。 -/
lemma cofiberFiberComparison_common (f : A ⟶ B) (g : A ⟶ C) :
    (cofiberFiberComparisonLower f g).pullback (SimplexCategory.δ (2 : Fin 4)).toOrderHom =
      (cofiberFiberComparisonUpper f g).pullback (SimplexCategory.δ (2 : Fin 4)).toOrderHom := by
  have hd :
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberLowerTriangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB f g) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionC f g)).simplex.pullback
        (SimplexCategory.δ (1 : Fin 3)).toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberUpperTriangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB f g) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionC f g)).simplex.pullback
        (SimplexCategory.δ (1 : Fin 3)).toOrderHom :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberLowerTriangle _ _).d₁.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberUpperTriangle _ _).d₁.symm
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberLowerTriangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB f g) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionC f g)).simplex.pullback
          (SimplexCategory.δ (1 : Fin 3)).toOrderHom)
        ⟨Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberLift f g), δ_ofHom _⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend_triangle_face_two _ _
    _ = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberUpperTriangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB f g) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionC f g)).simplex.pullback
          (SimplexCategory.δ (1 : Fin 3)).toOrderHom)
        ⟨Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberLift f g), δ_ofHom _⟩ :=
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend_congr hd (heq_of_eq rfl)
    _ = _ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend_triangle_face_two _ _).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
