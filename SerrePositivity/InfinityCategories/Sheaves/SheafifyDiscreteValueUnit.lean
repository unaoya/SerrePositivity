module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.SheafifyDiscreteValue

/-!
概要：離散値の同じ層化比較の成分は、元の反射単位を通常層化の単位へ送る。
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
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open Truncated.HomotopyCategory

namespace SerrePositivity.InfinityCategories.Sheaves

private lemma evaluation_eqToHom_commute {X : SSet.{u}} {L : X ⟶ X}
    (u : FunctorHom (𝟙 X) L) {x y : X _⦋0⦌} (h : x = y) :
    functorHomEvaluate u y ≫ eqToHom (congrArg HomotopyCategory.mk
      (congrArg (fun w => L.app (Opposite.op ⦋0⦌) w) h.symm)) =
      eqToHom (congrArg HomotopyCategory.mk h.symm) ≫ functorHomEvaluate u x := by
  subst y
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

private lemma unit_compare_endpoints {D : Type*} [Category* D]
    {x x' y y' z z' b : D} (hx : x = x') (hy : y' = y) (hz : z = z') (hb : b = y')
    (u : x ⟶ y) (u' : x' ⟶ y') (μ : y ⟶ z) (η : x ⟶ z) (m : x' ⟶ z')
    (hu : u' ≫ eqToHom hy = eqToHom hx.symm ≫ u)
    (hm : u ≫ μ = η) (he : η = eqToHom hx ≫ m ≫ eqToHom hz.symm) :
    (u' ≫ eqToHom hb.symm) ≫ (eqToHom hb ≫ eqToHom hy ≫ μ ≫ eqToHom hz) = m := by
  subst x' y' z' b
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at hu he ⊢
  exact (congrArg (fun w => w ≫ μ) hu).trans (hm.trans he)

/-- 離散値の同じ層化比較の成分は、元の反射単位を通常層化の単位へ送る。 -/
@[cite HTT "6.2.2.7" (partial := special) "小さい通常の site の離散係数の指定層化単位。"]
lemma sheafify_discrete_eq_hom_fac :
∀ {C : Type u} [SmallCategory C],
∀ (J : GrothendieckTopology C) (hJ : Sheafification J SpaceInfinity.{u})
  (P : Cᵒᵖ ⥤ Type u),
  sheafifyUnitHom J hJ (discretePresheaf P) ≫ (sheafify_discrete_eq J hJ P).hom =
    discretePresheafHom (CategoryTheory.toSheafify J P) := by
  intro C hC J hJ P
  let X := PresheafCat C SpaceInfinity.{u}
  let L := sheafificationFunctor J hJ
  let I := (discretePresheafInclusion C).val
  let S := presheafToSheaf J (Type u) ⋙ sheafToPresheaf J (Type u)
  let v := nerveVertex P
  let q : X _⦋0⦌ → X _⦋0⦌ := L.app (Opposite.op ⦋0⦌)
  let u := (Classical.choice hJ).unit
  let e := sheafifyDiscreteFunctorIso J hJ
  let μ := functorHomEvaluate e.hom v
  let h₁ : I.app _ v = functorVertex (discretePresheaf P) :=
    (discretePresheafInclusion C).property.1 P
  let h₂ : (nerveMap S ≫ I).app _ v = functorVertex (discretePresheaf (S.obj P)) :=
    (congrArg (fun w => I.app _ w) (nerveMap_app_mk₀ S P)).trans
      ((discretePresheafInclusion C).property.1 (S.obj P))
  let h₃ := functorVertex_sheafify J hJ (discretePresheaf P)
  let η := discreteSheafificationUnitHom J hJ
  let uI := functorHomPrecomp (𝟙 X) L I u
  have hh := congrArg (fun z => functorHomEvaluate z v)
    (sheafifyDiscreteFunctorIso_unit_fac J hJ)
  have hm : functorHomEvaluate u (I.app _ v) ≫ μ = functorHomEvaluate η v := by
    change functorHomEvaluate (uI ≫ e.hom) v = functorHomEvaluate η v at hh
    rw [functorHomEvaluate_comp] at hh
    exact (congrArg (fun z => z ≫ μ) (functorHomEvaluate_precomp u I v).symm).trans hh
  have he := discreteSheafificationUnitHom_evaluate J hJ P
  let m := discretePresheafHom (CategoryTheory.toSheafify J P)
  exact unit_compare_endpoints
    (congrArg HomotopyCategory.mk h₁) (congrArg HomotopyCategory.mk (congrArg q h₁.symm))
    (congrArg HomotopyCategory.mk h₂) (congrArg HomotopyCategory.mk h₃)
    (functorHomEvaluate u (I.app _ v)) (functorHomEvaluate u (functorVertex (discretePresheaf P)))
    μ (functorHomEvaluate η v) m (evaluation_eqToHom_commute u h₁) hm he

end SerrePositivity.InfinityCategories.Sheaves
