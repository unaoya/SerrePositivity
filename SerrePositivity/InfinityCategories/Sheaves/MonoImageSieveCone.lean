module

public import SerrePositivity.InfinityCategories.Sheaves.MonoImageSieveCommaEquivalence
public import SerrePositivity.InfinityCategories.Sheaves.SieveSectionsCriterion
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise

/-!
概要：単射の局所 comma の指定錐を、元の像篩の指定制限錐に接続する。
方針：通常の指定余単位による錐を全脚で比較し、同じ添字の同値で極限性を移す。
規約：HTT 6.2.2.6 の層条件の篩表示の法則。係数には準圏性だけを仮定する。
使われ方：S8 の局所単射の切断の不変性への局所入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {P Q : Cᵒᵖ ⥤ Type u}

/-- 同じ元の圏の射影の恒等余単位が与える通常の局所錐。 -/
def imageSieveCommaCone (φ : P ⟶ Q) (q : Q.Elements) :
    Cone (StructuredArrow.proj q φ.mapElements ⋙ Functor.Elements.π P) :=
  (Functor.RightExtension.mk (Functor.Elements.π Q) φ.mapElementsCompπIso.hom).coneAt q

/-- 元の通常の局所錐は、像篩の錐を同じ比較関手で制限したもの。 -/
lemma imageSieveCommaCone_eq (φ : P ⟶ Q) (q : Q.Elements) :
    imageSieveCommaCone φ q =
      (sieveCone (CategoryTheory.Presheaf.imageSieve φ q.val)).whisker
        (imageSieveCommaFunctor φ q) := by
  change Cone.mk q.obj _ = Cone.mk q.obj _
  congr 1
  apply NatTrans.ext
  funext a
  change a.hom.hom ≫ 𝟙 _ = a.hom.hom
  exact Category.comp_id _

variable {E : SSet.{u + 1}}

/-- 同じ係数で送った指定局所全錐。 -/
abbrev imageSieveCommaRestrictionCone (φ : P ⟶ Q) (q : Q.Elements) (O : Presheaf C E) :=
  ((nerveCone (imageSieveCommaCone φ q)).ulift).postcomp O

/-- 元の像篩の指定制限錐を、局所 comma の全錐として読み戻す。 -/
lemma imageSieveCommaRestrictionCone_val [Quasicategory E] (φ : P ⟶ Q) (q : Q.Elements)
    (O : Presheaf C E) :
    (restrictJoinCone (restrictionCone O (CategoryTheory.Presheaf.imageSieve φ q.val))
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (imageSieveCommaFunctor φ q)))).val =
      (imageSieveCommaRestrictionCone φ q O).val := by
  change (restrictJoinCone (((nerveCone _).ulift).postcomp O) _).val = _
  rw [uliftNerveCone_whisker_val, ← imageSieveCommaCone_eq]

/-- 単射の場合、元の像篩の降下と局所 comma の指定錐の極限性は同値。 -/
lemma imageSieveCommaRestrictionCone_isLimit_iff [Quasicategory E]
    (φ : P ⟶ Q) [Mono φ] (q : Q.Elements) (O : Presheaf C E) :
    IsLimitCone (imageSieveCommaRestrictionCone φ q O) ↔
      IsLimitCone (restrictionCone O (CategoryTheory.Presheaf.imageSieve φ q.val)) := by
  let j := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (imageSieveCommaFunctor φ q))
  have hj : IsQCatEquivalence j :=
    IsQCatEquivalence.ulift.{u, u + 1}
      (nerveQCatEquivalence (imageSieveCommaEquivalence φ q)).isQCatEquivalence
  exact ((isLimitCone_iff_restrict_equivalentShape j hj _).trans
    (isLimitCone_iff_of_cone_val_eq _ _ (imageSieveCommaRestrictionCone_val φ q O))).symm

/-- 局所全射な単射の各局所 comma は、同じ層の係数に対して指定極限錐を持つ。 -/
lemma imageSieveCommaRestrictionCone_isLimit [Quasicategory E]
    (J : GrothendieckTopology C) (φ : P ⟶ Q) [Mono φ]
    [CategoryTheory.Presheaf.IsLocallySurjective J φ] (q : Q.Elements)
    (O : Presheaf C E) (hO : IsSheaf J O) :
    IsLimitCone (imageSieveCommaRestrictionCone φ q O) :=
  (imageSieveCommaRestrictionCone_isLimit_iff φ q O).mpr
    (hO q.obj.unop _ (CategoryTheory.Presheaf.imageSieve_mem J φ q.val))

end SerrePositivity.InfinityCategories.Sheaves
