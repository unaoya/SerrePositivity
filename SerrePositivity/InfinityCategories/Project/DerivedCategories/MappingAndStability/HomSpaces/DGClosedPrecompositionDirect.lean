module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGGradedClosedPrecomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGComposition.DGClosedCompositionLinear
/-!
概要：対象の Small 性を使わず、閉次数零射による前合成鎖写像を構成する。
方針：斉次合成の各次数の線形写像と Leibniz 則を使う。
規約：対象・Hom・全整数次数を保持し、Yoneda 加群の構成を使わない。
使われ方：一般対象宇宙の自由 Hom と slice prism の係数自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

def dgClosedPrecompositionDirect {q x y : D}
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) :
    _root_.SerrePositivity.DifferentialGraded.homObject A D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject A D q y where
  f k := ModuleCat.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgZeroPrecomposeLinear A D (closedHomEquiv A D _ _ s).val k)
  comm' k n hkn := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose_d A D k n hkn a s

lemma dgClosedPrecompositionDirect_f {q x y : D}
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)
    (k : ℤ) (a : _root_.SerrePositivity.DifferentialGraded.GradedHom A x y k) :
    (dgClosedPrecompositionDirect A D (y := y) s).f k a =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D k a s := rfl

variable (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A E] (Q : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)
lemma dgClosedPrecompositionDirect_naturality {p q y : D}
    (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q) :
    dgClosedPrecompositionDirect A D (y := y) r ≫ Q.map p y =
      Q.map q y ≫ dgClosedPrecompositionDirect A E (q := Q.obj p) (x := Q.obj q)
        (y := Q.obj y) (Q.onClosed.map r) := by
  apply HomologicalComplex.Hom.ext
  funext k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorGradedPrecompose_map A D E Q k a r
end SerrePositivity.InfinityCategories.Project.DerivedCategories
