module

public import SerrePositivity.InfinityCategories.Sheaves.SieveSiteConeComparison
public import SerrePositivity.InfinityCategories.Sheaves.SheafSiteInvariance

/-!
概要：係数と同じ宇宙の nerve 上で、元の被覆篩の指定制限錐を比較する。
方針：既存の篩圏の同値と通常の錐の自然性を、宇宙の持ち上げなしで用いる。
  文献対応：HTT 6.2.2.6、Kerodon §7.1（Tag 02K2）の同値な site 間の層条件。
規約：大きい site の AsSmall 表示でも係数の宇宙を上げないための補助表示。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
variable {E : SSet.{u}} [Quasicategory E]

/-- 同じ宇宙の係数に値を取る前層の、元の篩上の制限図式。 -/
def nativeRestriction (O : nerve Cᵒᵖ ⟶ E) {U : C} (S : Sieve U) :
    nerve (sieveCategory S)ᵒᵖ ⟶ E := nerveMap (sieveDiagram S) ≫ O

/-- 同じ宇宙での制限錐。頂点だけでなく、元のすべての脚を保持する。 -/
def nativeRestrictionCone (O : nerve Cᵒᵖ ⟶ E) {U : C} (S : Sieve U) :
    JoinCone (nativeRestriction O S) := (nerveCone (sieveCone S)).postcomp O

/-- 係数と同じ宇宙に表示した site 上の、すべての被覆篩に対する層条件。 -/
def NativeIsSheaf (J : GrothendieckTopology C) (O : nerve Cᵒᵖ ⟶ E) : Prop :=
  ∀ (U : C) (S : Sieve U), S ∈ J U → IsLimitCone (nativeRestrictionCone O S)

/-- 制限の比較は元の錐全体の等式であり、係数の宇宙を変更しない。 -/
lemma nativeRestrictionCone_site_val (F : C ⥤ D) {U : C}
    (S : Sieve (F.obj U)) (O : nerve Dᵒᵖ ⟶ E) :
    (restrictJoinCone (nativeRestrictionCone O S) (nerveMap (sieveSiteFunctor F S).op)).val =
      (nativeRestrictionCone (nerveMap F.op ≫ O) (S.functorPullback F)).val := by
  change (_ ≫ (nerveCone (sieveCone S)).val) ≫ O = _
  rw [nerveCone_whisker, ← sieveSiteFunctor_cone, ← nerveCone_mapCone]
  rfl

/-- 同値な site の元の被覆篩で、指定制限錐の極限性を保存し反映する。 -/
lemma isLimit_nativeRestrictionCone_site_iff (e : C ≌ D) {U : C}
    (S : Sieve (e.functor.obj U)) (O : nerve Dᵒᵖ ⟶ E) :
    IsLimitCone (nativeRestrictionCone (nerveMap e.functor.op ≫ O)
      (S.functorPullback e.functor)) ↔ IsLimitCone (nativeRestrictionCone O S) := by
  let j := nerveMap (sieveSiteFunctor e.functor S).op
  have hj : IsQCatEquivalence j :=
    (nerveQCatEquivalence (sieveSiteEquivalence e S).op).isQCatEquivalence
  have hv := nativeRestrictionCone_site_val e.functor S O
  exact (SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_iff_of_cone_val_eq _ _ hv).symm.trans
    (isLimitCone_iff_restrict_equivalentShape j hj (nativeRestrictionCone O S)).symm

/-- 同じ全関手同型に沿い、元の被覆篩の錐を同時に移す。 -/
lemma NativeIsSheaf.of_functorIso {J : GrothendieckTopology C}
    {O P : nerve Cᵒᵖ ⟶ E} (h : NativeIsSheaf J O) (e : FunctorIso O P) :
    NativeIsSheaf J P := by
  intro U S hS
  exact (h U S hS).of_functorIso (e.precomp (nerveCone (sieveCone S)).val)

/-- 被覆を保つ site 同値に沿い、同じ宇宙の層条件を移す。 -/
lemma NativeIsSheaf.reindex_of_equivalence (e : C ≌ D)
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (hf : CoverPreserving J K e.functor) {O : nerve Dᵒᵖ ⟶ E}
    (h : NativeIsSheaf K O) : NativeIsSheaf J (nerveMap e.functor.op ≫ O) := by
  intro U S hS
  have h' := (isLimit_nativeRestrictionCone_site_iff e (S.functorPushforward e.functor) O).mpr
    (h _ _ (hf.cover_preserve hS))
  rw [Sieve.functorPullback_functorPushforward_eq e.functor] at h'
  exact h'

/-- 両向きの元の被覆保存性から、同じ宇宙の層条件を保存し反映する。 -/
theorem nativeIsSheaf_reindex_equivalence_iff (e : C ≌ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (hf : CoverPreserving J K e.functor) (hg : CoverPreserving K J e.inverse)
    (O : nerve Dᵒᵖ ⟶ E) :
    NativeIsSheaf J (nerveMap e.functor.op ≫ O) ↔ NativeIsSheaf K O := by
  constructor
  · intro h
    have h' := h.reindex_of_equivalence e.symm hg
    change NativeIsSheaf K (nerveMap e.inverse.op ≫ (nerveMap e.functor.op ≫ O)) at h'
    have i : FunctorIso (nerveMap e.inverse.op ≫ nerveMap e.functor.op)
        (𝟙 (nerve Dᵒᵖ)) := (nerveQCatEquivalence e.op).invHomIso
    have i' : FunctorIso (nerveMap e.inverse.op ≫ (nerveMap e.functor.op ≫ O)) O := by
      simpa only [Category.assoc, Category.id_comp] using i.postcomp O
    exact NativeIsSheaf.of_functorIso (C := D) (E := E) h' i'
  · exact fun h ↦ h.reindex_of_equivalence e hf

end SerrePositivity.InfinityCategories.Sheaves
