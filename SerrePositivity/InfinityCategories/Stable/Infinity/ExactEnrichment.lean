module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Stable.Verdier.StableCategories
public import SerrePositivity.InfinityCategories.F1.Categories.QCatSimplicial

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
namespace SerrePositivity.InfinityCategories.Stable.Infinity
open SerrePositivity.KST.LocalizingInvariants

/-- 内部 Hom の合成は、頂点では元の関手の合成。 -/
lemma internalComp_vertex {A B C : SSet.{u}} (F : A ⟶ B) (G : B ⟶ C) :
    (MonoidalClosed.comp A B C).app (Opposite.op ⦋0⦌)
      (functorVertex F, functorVertex G) = functorVertex (F ≫ G) := by
  rfl

/-- 恒等完全関手を単位からの射として表示する。 -/
def exactIdentity (A : StableCategory.{u}) :
    (𝟙_ SSet.{u}) ⟶ (exactFunctors A A : SSet.{u}) :=
  fullSubcomplexLift (IsExactVertex A A) (MonoidalClosed.id A.obj) (by
    intro v
    change PUnit at v
    have hv : (v : PUnit) = PUnit.unit := Subsingleton.elim _ _
    subst v
    change IsExactFunctor ((functorVertexEquiv A.obj A.obj).symm
      ((functorVertexEquiv A.obj A.obj) (𝟙 A.obj)))
    rw [Equiv.symm_apply_apply]
    infer_instance)

/-- 完全関手の単体的合成。 -/
def exactComposition (A B C : StableCategory.{u}) :
    (exactFunctors A B : SSet.{u}) ⊗ (exactFunctors B C : SSet.{u}) ⟶
      (exactFunctors A C : SSet.{u}) :=
  fullSubcomplexLift (IsExactVertex A C)
    (((exactFunctors A B).ι ⊗ₘ (exactFunctors B C).ι) ≫
      MonoidalClosed.comp A.obj B.obj C.obj) (by
    intro v
    let F := (exactFunctorVertexEquiv A B).symm v.1
    let G := (exactFunctorVertexEquiv B C).symm v.2
    have hF : v.1.val = functorVertex F.hom :=
      congrArg Subtype.val ((exactFunctorVertexEquiv A B).apply_symm_apply v.1).symm
    have hG : v.2.val = functorVertex G.hom :=
      congrArg Subtype.val ((exactFunctorVertexEquiv B C).apply_symm_apply v.2).symm
    change IsExactVertex A C ((MonoidalClosed.comp A.obj B.obj C.obj).app _
      (v.1.val, v.2.val))
    rw [hF, hG, internalComp_vertex]
    change IsExactFunctor ((functorVertexEquiv A.obj C.obj).symm
      ((functorVertexEquiv A.obj C.obj) (F.hom ≫ G.hom)))
    rw [Equiv.symm_apply_apply]
    infer_instance)

/-- 包含の後では周囲の内部 Hom の合成に一致する。 -/
lemma exactComposition_ι (A B C : StableCategory.{u}) :
    exactComposition A B C ≫ (exactFunctors A C).ι =
      ((exactFunctors A B).ι ⊗ₘ (exactFunctors B C).ι) ≫
        MonoidalClosed.comp A.obj B.obj C.obj := fullSubcomplexLift_ι _ _ _

/-- 恒等完全関手の包含は内部 Hom の単位そのもの。 -/
lemma exactIdentity_ι (A : StableCategory.{u}) :
    exactIdentity A ≫ (exactFunctors A A).ι = MonoidalClosed.id A.obj :=
  fullSubcomplexLift_ι _ _ _

/-- 完全関手と全自然変換による豊穣構造。 -/
instance stableCategory_enrichedCategory : EnrichedCategory SSet.{u} StableCategory.{u} where
  Hom A B := (exactFunctors A B : SSet.{u})
  id := exactIdentity
  comp := exactComposition
  id_comp A B := by
    apply (cancel_mono (exactFunctors A B).ι).1
    simp only [Category.assoc, exactComposition_ι]
    rw [whiskerRight_comp_tensorHom_assoc, exactIdentity_ι]
    rw [leftUnitor_inv_comp_tensorHom_assoc, MonoidalClosed.id_comp]
    simp
  comp_id A B := by
    apply (cancel_mono (exactFunctors A B).ι).1
    simp only [Category.assoc, exactComposition_ι]
    rw [whiskerLeft_comp_tensorHom_assoc, exactIdentity_ι]
    rw [rightUnitor_inv_comp_tensorHom_assoc, MonoidalClosed.comp_id]
    simp
  assoc A B C D := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro v
    apply Subtype.ext
    rfl

end SerrePositivity.InfinityCategories.Stable.Infinity

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Infinity.exactComposition (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactComposition := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.exactComposition

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactComposition_ι := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.exactComposition_ι

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Infinity.exactIdentity (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactIdentity := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.exactIdentity

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactIdentity_ι := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.exactIdentity_ι

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.internalComp_vertex := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.internalComp_vertex

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableCategory_enrichedCategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableCategory_enrichedCategory := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableCategory_enrichedCategory

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactComposition._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.exactComposition._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactIdentity._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.exactIdentity._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableCategory_enrichedCategory._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableCategory_enrichedCategory._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableCategory_enrichedCategory._proof_2 := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableCategory_enrichedCategory._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableCategory_enrichedCategory._proof_3 := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableCategory_enrichedCategory._proof_3
