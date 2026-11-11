module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategories
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCatSimplicial

/-!
概要：安定 ∞ 圏と完全関手の単体的な合成。
方針：内部 Hom の合成を完全関手の全部分複体に制限する。
規約：自然変換は商にしない。使われ方：安定 ∞ 圏の coherent nerve。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity
open _root_.SerrePositivity.KST.LocalizingInvariants

/-- 内部 Hom の合成は、頂点では元の関手の合成。 -/
lemma internalComp_vertex {A B C : SSet.{u}} (F : A ⟶ B) (G : B ⟶ C) :
    (MonoidalClosed.comp A B C).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (F ≫ G) := by
  rfl

/-- 恒等完全関手を単位からの射として表示する。 -/
def exactIdentity (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    (𝟙_ SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A A : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsExactVertex A A) (MonoidalClosed.id A.obj) (by
    intro v
    change PUnit at v
    have hv : (v : PUnit) = PUnit.unit := Subsingleton.elim _ _
    subst v
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A.obj A.obj).symm
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A.obj A.obj) (𝟙 A.obj)))
    rw [Equiv.symm_apply_apply]
    infer_instance)

/-- 完全関手の単体的合成。 -/
def exactComposition (A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B : SSet.{u}) ⊗ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors B C : SSet.{u}) ⟶
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A C : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsExactVertex A C)
    (((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B).ι ⊗ₘ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors B C).ι) ≫
      MonoidalClosed.comp A.obj B.obj C.obj) (by
    intro v
    let F := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv A B).symm v.1
    let G := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv B C).symm v.2
    have hF : v.1.val = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom :=
      congrArg Subtype.val ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv A B).apply_symm_apply v.1).symm
    have hG : v.2.val = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G.hom :=
      congrArg Subtype.val ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv B C).apply_symm_apply v.2).symm
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsExactVertex A C ((MonoidalClosed.comp A.obj B.obj C.obj).app _
      (v.1.val, v.2.val))
    rw [hF, hG, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.internalComp_vertex]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A.obj C.obj).symm
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A.obj C.obj) (F.hom ≫ G.hom)))
    rw [Equiv.symm_apply_apply]
    infer_instance)

/-- 包含の後では周囲の内部 Hom の合成に一致する。 -/
lemma exactComposition_ι (A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactComposition A B C ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A C).ι =
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B).ι ⊗ₘ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors B C).ι) ≫
        MonoidalClosed.comp A.obj B.obj C.obj := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 恒等完全関手の包含は内部 Hom の単位そのもの。 -/
lemma exactIdentity_ι (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactIdentity A ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A A).ι = MonoidalClosed.id A.obj :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 完全関手と全自然変換による豊穣構造。 -/
instance stableCategory_enrichedCategory : EnrichedCategory SSet.{u} _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u} where
  Hom A B := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B : SSet.{u})
  id := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactIdentity
  comp := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactComposition
  id_comp A B := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B).ι).1
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactComposition_ι]
    rw [whiskerRight_comp_tensorHom_assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactIdentity_ι]
    rw [leftUnitor_inv_comp_tensorHom_assoc, MonoidalClosed.id_comp]
    simp
  comp_id A B := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B).ι).1
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactComposition_ι]
    rw [whiskerLeft_comp_tensorHom_assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactIdentity_ι]
    rw [rightUnitor_inv_comp_tensorHom_assoc, MonoidalClosed.comp_id]
    simp
  assoc A B C D := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro v
    apply Subtype.ext
    rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactComposition (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactComposition := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactComposition

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactComposition_ι := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactComposition_ι

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactIdentity (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactIdentity := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactIdentity

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactIdentity_ι := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactIdentity_ι

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.internalComp_vertex := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.internalComp_vertex

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableCategory_enrichedCategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableCategory_enrichedCategory := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableCategory_enrichedCategory

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactComposition._proof_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactComposition._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactIdentity._proof_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactIdentity._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableCategory_enrichedCategory._proof_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableCategory_enrichedCategory._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableCategory_enrichedCategory._proof_2 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableCategory_enrichedCategory._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableCategory_enrichedCategory._proof_3 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableCategory_enrichedCategory._proof_3
