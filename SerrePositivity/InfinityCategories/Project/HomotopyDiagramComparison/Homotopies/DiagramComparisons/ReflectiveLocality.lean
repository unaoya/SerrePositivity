module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LocalObjects
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveLocalObjects

/-!
概要：既存の反射の局所対象を、元の全単位成分に対する写像空間の局所性で特徴づける。
方針：包含の全忠実性で単位比較の同値を反映し、元の単位の両逆を回収する。
規約：与えられた反射の性質のみ。反射の存在定理ではない。使われ方：HTT 5.5.4.2。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {X : SSet.{u}} [Quasicategory X]

/-- 反射の包含の像は元の全ての単位成分に対して局所。 -/
lemma reflectiveUnit_isLocalForHom_inclusion {P : X _⦋0⦌ → Prop}
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory X P) (x : X _⦋0⦌)
    (y : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalForHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitComponent r.unit x) y.val := by
  have h := (r.adjunction.unitMappingSpaceCondition x y).isQCatEquivalence
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitPinchedMap_formula] at h
  exact (r.inclusion_fullyFaithful
    (r.reflector.app (Opposite.op ⦋0⦌) x) y).isQCatEquivalence.cancel_left h

/-- 反射の局所対象は元の全ての単位成分に対して局所。 -/
lemma reflectiveUnit_isLocalForHom {P : X _⦋0⦌ → Prop}
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory X P) {z : X _⦋0⦌} (hz : r.IsLocal z) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalForHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitComponent r.unit x) z := by
  obtain ⟨y, ⟨e⟩⟩ := (r.isLocal_iff_essentialImage z).mp hz
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLocalForHom_iff_of_vertexIso _ e).mp (reflectiveUnit_isLocalForHom_inclusion r x y)

/-- 反射の局所対象と、全ての単位成分への写像空間による局所性は同値。 -/
lemma reflective_isLocal_iff_unit_local {P : X _⦋0⦌ → Prop}
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory X P) (z : X _⦋0⦌) :
    r.IsLocal z ↔ ∀ x : X _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalForHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitComponent r.unit x) z := by
  constructor
  · intro hz x
    exact reflectiveUnit_isLocalForHom r hz x
  · intro h
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isIso_of_isLocalForHom_source_target (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitComponent r.unit z) (h z)
      (reflectiveUnit_isLocalForHom_inclusion r z (r.reflector.app (Opposite.op ⦋0⦌) z))

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
