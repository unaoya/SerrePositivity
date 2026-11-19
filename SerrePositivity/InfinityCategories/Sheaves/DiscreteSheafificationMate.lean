module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.DiscreteSheafificationUnitSpecified
public import SerrePositivity.InfinityCategories.Sheaves.DiscreteSheafCondition
public import SerrePositivity.InfinityCategories.Sheaves.SheafifyUnit
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FullyFaithfulHomComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomPostcompIdentity
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluationNaturality

/-!
概要：指定された全単位から、同じ単位の式を満たす全 mate を得る。
方針：同じ通常層化の単位の全円柱とその頂点成分を使う。
  文献対応：HTT 6.2.2.7・5.5.4.15。
使われ方：離散係数の指定層化の全比較。
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open Truncated.HomotopyCategory

namespace SerrePositivity.InfinityCategories.Sheaves

/-- 単位を全成分が層である図式に沿って前合成すると、全関手圏で可逆。 -/
lemma sheafification_unit_precomp_local_isIso
    {C : Type u} [SmallCategory C] {D : SSet.{u + 1}}
    (J : GrothendieckTopology C) (hJ : Sheafification J SpaceInfinity.{u})
    (B : D ⟶ PresheafCat C SpaceInfinity.{u})
    (hB : ∀ v : D _⦋0⦌, sheafProperty J (B.app _ v)) :
    IsIso (functorHomPrecomp (𝟙 (PresheafCat C SpaceInfinity.{u}))
      (sheafificationFunctor J hJ) B (Classical.choice hJ).unit) := by
  let r := Classical.choice hJ
  let α := functorHomPrecomp (𝟙 (PresheafCat C SpaceInfinity.{u}))
    (sheafificationFunctor J hJ) B r.unit
  change IsIso α
  apply functorHom_isIso_of_components
  intro v
  have hv := hB v
  let z := B.app (Opposite.op ⦋0⦌) v
  have hl := r.isLocal_inclusion ⟨z, by
    intro w
    have hw : w = 𝟙 _ := Subsingleton.elim _ _
    simpa only [hw, op_id, Functor.map_id_apply] using hv⟩
  change IsIso (functorHomEvaluate r.unit z) at hl
  have he : IsIso (functorHomEvaluate α v) :=
    (functorHomEvaluate_precomp r.unit B v).symm ▸ hl
  simpa only [functorHomEvaluate, isIso_comp_left_iff, isIso_comp_right_iff] using he

/-- 通常層化を離散前層として読んだ図式の各頂点は層。 -/
lemma discreteSheafificationTarget_mem {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) :
    let S := presheafToSheaf J (Type u) ⋙ sheafToPresheaf J (Type u)
    let I := (discretePresheafInclusion C).val
    ∀ v, sheafProperty J ((nerveMap S ≫ I).app (Opposite.op ⦋0⦌) v) := by
  intro S I v
  let P := nerveEquiv v
  have hv : nerveVertex P = v := nerveEquiv.left_inv v
  rw [← hv]
  have h : (nerveMap S ≫ I).app _ (nerveVertex P) =
      functorVertex (discretePresheaf (S.obj P)) :=
    (congrArg (fun w => I.app _ w) (nerveMap_app_mk₀ S P)).trans
      ((discretePresheafInclusion C).property.1 (S.obj P))
  rw [h]
  change IsSheaf J ((functorVertexEquiv _ _).symm
    ((functorVertexEquiv _ _) (discretePresheaf (S.obj P))))
  rw [Equiv.symm_apply_apply]
  exact (isSheaf_discretePresheaf_iff J (S.obj P)).mpr
    ((presheafToSheaf J (Type u)).obj P).property

/-- 指定された全単位から、同じ単位の式を満たす全 mate を得る。 -/
@[cite HTT "6.2.2.7" (partial := special) "小さい通常の site の離散係数の指定層化単位。"]
lemma discreteSheafification_mate_exists_specified :
∀ {C : Type u} [SmallCategory C]
 (J : GrothendieckTopology C) (hJ : Sheafification J SpaceInfinity.{u}),
let S := presheafToSheaf J (Type u) ⋙ sheafToPresheaf J (Type u)
let I := (discretePresheafInclusion C).val
∀ (η : FunctorHom I (nerveMap S ≫ I))
 (hη : ∀ P : Cᵒᵖ ⥤ Type u,
   let h₁ := (discretePresheafInclusion C).property.1 P
   let h₂ : (nerveMap S ≫ I).app _ (nerveVertex P) =
       functorVertex (discretePresheaf (S.obj P)) :=
     (congrArg (fun v => I.app _ v) (nerveMap_app_mk₀ S P)).trans
       ((discretePresheafInclusion C).property.1 (S.obj P))
   functorHomEvaluate η (nerveVertex P) =
     eqToHom (congrArg HomotopyCategory.mk h₁) ≫
     discretePresheafHom (CategoryTheory.toSheafify J P) ≫
     eqToHom (congrArg HomotopyCategory.mk h₂.symm))
 (hηL : IsIso (functorHomPostcomp I (nerveMap S ≫ I)
   (sheafificationFunctor J hJ) η)),
 ∃ m : FunctorHom (I ≫ sheafificationFunctor J hJ) (nerveMap S ≫ I),
  functorHomPrecomp (𝟙 (PresheafCat C SpaceInfinity.{u}))
    (sheafificationFunctor J hJ) I (Classical.choice hJ).unit ≫ m = η := by
  intro C hC J hJ S I η _hη _hηL
  let X := PresheafCat C SpaceInfinity.{u}
  let L := sheafificationFunctor J hJ
  let T := nerveMap S ≫ I
  let u := (Classical.choice hJ).unit
  let uI := functorHomPrecomp (𝟙 X) L I u
  let uT := functorHomPrecomp (𝟙 X) L T u
  let ηL := functorHomPostcomp I T L η
  letI : IsIso uT := sheafification_unit_precomp_local_isIso J hJ T
    (discreteSheafificationTarget_mem J)
  let m := ηL ≫ inv uT
  refine ⟨m, ?_⟩
  have h := functorHom_whisker_exchange_typed η u
  rw [functorHom_postcomp_id η] at h
  change η ≫ uT = uI ≫ ηL at h
  change uI ≫ (ηL ≫ inv uT) = η
  calc
    _ = (uI ≫ ηL) ≫ inv uT := (Category.assoc uI ηL (inv uT)).symm
    _ = (η ≫ uT) ≫ inv uT := congrArg (fun z : FunctorHom I (T ≫ L) => z ≫ inv uT) h.symm
    _ = η ≫ (uT ≫ inv uT) := Category.assoc η uT (inv uT)
    _ = η ≫ 𝟙 _ := congrArg (η ≫ ·) (IsIso.hom_inv_id uT)
    _ = η := Category.comp_id η

end SerrePositivity.InfinityCategories.Sheaves
