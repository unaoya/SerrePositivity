module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGDoubleOpposite
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGFunctors.DGFunctorCommaProjections
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelUniversalCounit
public import SerrePositivity.DifferentialGraded.Category.ObjectImage
/-!
概要：普遍余単位の実比較対象に、全比較 cochain を持つ実 dg comma 構造を与える。
方針：一般の dg comma を反対 dg 圏へ適用し、対象ラベルに沿う充満像を取る。
規約：大きい対象型の Small 性を要求しない。使われ方：coherent な一般 RHom 右随伴。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C E : Type v) [DGCategory R C] [DGCategory R E]
  (F : DGFunctor R C E)
/-- 普遍余単位を同じ標的と併せて保持する実対象ラベル。 -/
structure DGUniversalCommaLabel where
  target : E
  universal : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniversalCounit R C E F target

/-- 同じ余単位を一般の反対 dg comma の比較射へ移す。 -/
def dgUniversalCommaDualLabel (x : DGUniversalCommaLabel R C E F) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R Cᵒᵖ Eᵒᵖ F.op where
  source := Opposite.op x.universal.source
  replacement := Opposite.op x.target
  augmentation := (forgetEnrichmentOppositeEquivalence (Complex R) E).inverse.map
    x.universal.counit.op
/-- 普遍余単位の全比較 cochain を保持する実 dg 圏。 -/
abbrev DGUniversalComma := _root_.SerrePositivity.InfinityCategories.DGObjectImage
  (fun x : DGUniversalCommaLabel R C E F => Opposite.op (dgUniversalCommaDualLabel R C E F x))

/-- 同じ標的対象と全標的 Hom を回収する実 dg 射影。 -/
def dgUniversalCommaTarget : DGFunctor R (DGUniversalComma R C E F) E :=
  ((_root_.SerrePositivity.InfinityCategories.dgObjectImageEvaluation R _).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacement R Cᵒᵖ Eᵒᵖ F.op).op).comp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgDoubleOppositeDown R E)
/-- 同じ余単位の始域対象と全始域 Hom を回収する実 dg 射影。 -/
def dgUniversalCommaSource : DGFunctor R (DGUniversalComma R C E F) C :=
  ((_root_.SerrePositivity.InfinityCategories.dgObjectImageEvaluation R _).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSource R Cᵒᵖ Eᵒᵖ F.op).op).comp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgDoubleOppositeDown R C)
/-- 標的射影は同じラベルの実標的を回収する。 -/
lemma dgUniversalCommaTarget_obj (x : DGUniversalComma R C E F) :
    (dgUniversalCommaTarget R C E F).obj x = x.label.target := rfl
/-- 始域射影は同じ普遍余単位の実始域を回収する。 -/
lemma dgUniversalCommaSource_obj (x : DGUniversalComma R C E F) :
    (dgUniversalCommaSource R C E F).obj x = x.label.universal.source := rfl
/-- 普遍余単位の局所存在から実標的射影の対象上全射性を得る。 -/
lemma dgUniversalCommaTarget_obj_surjective
    (h : ∀ y : E, Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniversalCounit R C E F y)) :
    Function.Surjective (dgUniversalCommaTarget R C E F).obj := by
  intro y
  obtain ⟨e⟩ := h y
  exact ⟨⟨⟨y, e⟩⟩, rfl⟩
end SerrePositivity.InfinityCategories.Project.DerivedCategories
