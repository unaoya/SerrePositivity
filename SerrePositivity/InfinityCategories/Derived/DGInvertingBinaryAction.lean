module
public import SerrePositivity.InfinityCategories.Derived.DGFiniteBinaryEvaluation
public import SerrePositivity.InfinityCategories.Derived.PinchedFamilyCompositionEvaluation
/-!
概要：任意有限二商 Hom 族について、全降下選択を同時に動かす実作用族の合成を証明する。
方針：同じ三実評価族への全選択空間上の同型を、任意共通選択パラメータ上で展開する。
規約：三対象対の選択を独立に動かせる。使われ方：局所化延長の二入力合成整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
/-- 商 Hom の作用を、商 Hom パラメータと任意の降下選択パラメータ上で同時に評価する。 -/
def dgInvertingHomFamilyValue (P : Set D) (x y : D) {K Y S : SSet.{max u v}}
    (F : dgNerve A D ⟶ Y)
    (b : K ⟶ DGNerve.pinchedHom A (DGQuotient.QuotientObject D P)
      ((DGQuotient.inclusion A D P).obj x) ((DGQuotient.inclusion A D P).obj y))
    (p : S ⟶ dgInvertingHomDescentSpace A D P x y F) :
    K ⊗ S ⟶ pinchedHom (F.app (Opposite.op ⦋0⦌) (Simplex.vertex x))
      (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y)) :=
  uncurry (p ≫ (dgInvertingHomActionFamily A D P x y F ≫ (pre b).app _))
variable (P : Set D) (x y z : D) {K Y : SSet.{max u v}} [Quasicategory Y]
variable (F : dgNerve A D ⟶ Y)
variable (b : K ⟶ DGNerve.pinchedHom A (DGQuotient.QuotientObject D P)
  ((DGQuotient.inclusion A D P).obj x) ((DGQuotient.inclusion A D P).obj y))
variable (c : K ⟶ DGNerve.pinchedHom A (DGQuotient.QuotientObject D P)
  ((DGQuotient.inclusion A D P).obj y) ((DGQuotient.inclusion A D P).obj z))
/-- 同じ実三評価を持つ三作用族は、任意の共通選択パラメータ上で合成する。 -/
lemma dgInvertingBinaryAction_of_evaluation
    (E : DGFiniteBinaryEvaluation A D P x y z F b c)
    (S : SSet.{max u v}) (p₁ : S ⟶ dgInvertingHomDescentSpace A D P x y F)
    (p₂ : S ⟶ dgInvertingHomDescentSpace A D P y z F)
    (p₃ : S ⟶ dgInvertingHomDescentSpace A D P x z F) :
    intervalFamilyHom (dgInvertingHomFamilyValue A D P x y F b p₁ ≫
      pinchedHomToIntervalMappingSpace _ _) ≫
    intervalFamilyHom (dgInvertingHomFamilyValue A D P y z F c p₂ ≫
      pinchedHomToIntervalMappingSpace _ _) =
    intervalFamilyHom (dgInvertingHomFamilyValue A D P x z F
      (pinchedHomCompositionFamily b c) p₃ ≫ pinchedHomToIntervalMappingSpace _ _) :=
  pinchedFamilyComposition_evaluation _ _ _
    E.evaluation.first.value E.evaluation.second.value E.evaluation.composite.value
    E.evaluation.firstIso E.evaluation.secondIso E.evaluation.compositeIso
    (Truncated.HomotopyCategory.homMk_comp_homMk E.evaluation.triangle) S p₁ p₂ p₃
/-- 任意有限二商 Hom 族の作用は、全選択空間を同時に動かすパラメータ全体で合成する。 -/
lemma dgInvertingBinaryAction_comp [K.Finite] (hP : DGQuotient.localKFlat A D P)
    (hF : InvertsEdges F (dgVerdierEdges A D P))
    (S : SSet.{max u v}) (p₁ : S ⟶ dgInvertingHomDescentSpace A D P x y F)
    (p₂ : S ⟶ dgInvertingHomDescentSpace A D P y z F)
    (p₃ : S ⟶ dgInvertingHomDescentSpace A D P x z F) :
    intervalFamilyHom (dgInvertingHomFamilyValue A D P x y F b p₁ ≫
      pinchedHomToIntervalMappingSpace _ _) ≫
    intervalFamilyHom (dgInvertingHomFamilyValue A D P y z F c p₂ ≫
      pinchedHomToIntervalMappingSpace _ _) =
    intervalFamilyHom (dgInvertingHomFamilyValue A D P x z F
      (pinchedHomCompositionFamily b c) p₃ ≫ pinchedHomToIntervalMappingSpace _ _) := by
  obtain ⟨E⟩ := dgFiniteBinaryEvaluation_nonempty A D P x y z F b c hP hF
  exact dgInvertingBinaryAction_of_evaluation A D P x y z F b c E S p₁ p₂ p₃
/-- 同じ全選択パラメータ上で、三作用族の実合成三角形を取れる。 -/
lemma dgInvertingBinaryAction_triangle_nonempty [K.Finite] (hP : DGQuotient.localKFlat A D P)
    (hF : InvertsEdges F (dgVerdierEdges A D P))
    (S : SSet.{max u v}) (p₁ : S ⟶ dgInvertingHomDescentSpace A D P x y F)
    (p₂ : S ⟶ dgInvertingHomDescentSpace A D P y z F)
    (p₃ : S ⟶ dgInvertingHomDescentSpace A D P x z F) :
    Nonempty (Truncated.Edge.CompStruct
      (intervalFamilyEdge (dgInvertingHomFamilyValue A D P x y F b p₁ ≫
        pinchedHomToIntervalMappingSpace _ _))
      (intervalFamilyEdge (dgInvertingHomFamilyValue A D P y z F c p₂ ≫
        pinchedHomToIntervalMappingSpace _ _))
      (intervalFamilyEdge (dgInvertingHomFamilyValue A D P x z F
        (pinchedHomCompositionFamily b c) p₃ ≫ pinchedHomToIntervalMappingSpace _ _))) := by
  apply compStruct_nonempty_of_homMk_fac
  exact dgInvertingBinaryAction_comp A D P x y z F b c hP hF S p₁ p₂ p₃
end SerrePositivity.InfinityCategories
