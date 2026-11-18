module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.DiscreteSheafificationUnitInverted

/-!
概要：同じ通常層化の単位の成分式と、層化後の可逆性を同時に得る。
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
open Truncated.HomotopyCategory

namespace SerrePositivity.InfinityCategories.Sheaves

private lemma undo_endpoint_transport {D : Type*} [Category* D] {a b x y : D}
    (f : a ⟶ b) (g : x ⟶ y) (hx : a = x) (hy : b = y)
    (h : eqToHom hx.symm ≫ f ≫ eqToHom hy = g) :
    f = eqToHom hx ≫ g ≫ eqToHom hy.symm := by
  subst x y
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h

/-- 通常層化の全単位の頂点評価は、二つの端点を移した同じ離散の射。 -/
lemma discreteSheafificationUnitHom_evaluate
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (hJ : Sheafification J SpaceInfinity.{u}) :
    let S := presheafToSheaf J (Type u) ⋙ sheafToPresheaf J (Type u)
    let I := (discretePresheafInclusion C).val
    ∀ P : Cᵒᵖ ⥤ Type u,
      let h₁ := (discretePresheafInclusion C).property.1 P
      let h₂ : (nerveMap S ≫ I).app _ (nerveVertex P) =
          functorVertex (discretePresheaf (S.obj P)) := by
        exact (congrArg (fun v => I.app _ v) (nerveMap_app_mk₀ S P)).trans
          ((discretePresheafInclusion C).property.1 (S.obj P))
      functorHomEvaluate (discreteSheafificationUnitHom J hJ) (nerveVertex P) =
        eqToHom (congrArg (fun v => HomotopyCategory.mk v) h₁) ≫
          discretePresheafHom (CategoryTheory.toSheafify J P) ≫
          eqToHom (congrArg (fun v => HomotopyCategory.mk v) h₂.symm) := by
  intro S I P h₁ h₂
  let H := ordinarySheafificationUnit_postHomotopy J hJ
  let φ := CategoryTheory.toSheafify J P
  let a := (simplicialHomotopyVertexEdge H (nerveVertex P)).toTruncated
  let b := (((nerve.edgeMk φ).map I).ofEq
    ((discretePresheafInclusion C).property.1 P)
    ((discretePresheafInclusion C).property.1 (S.obj P))).toTruncated
  have hab : a.edge = b.edge := ordinarySheafificationUnit_postHomotopy_component J hJ P
  have hh := homMk_transport h₁ h₂ a b hab
  have hh' : homMk a = eqToHom (congrArg HomotopyCategory.mk h₁) ≫
      discretePresheafHom φ ≫ eqToHom (congrArg HomotopyCategory.mk h₂.symm) :=
    undo_endpoint_transport (homMk a) (homMk b)
      (congrArg HomotopyCategory.mk h₁) (congrArg HomotopyCategory.mk h₂) hh
  exact (functorHomEvaluate_homotopy H (nerveVertex P)).trans hh'

/-- 同じ通常層化の単位の成分式と、層化後の可逆性を同時に得る。 -/
@[cite HTT "6.2.2.7" (partial := special) "小さい通常の site の離散係数の指定層化単位。"]
lemma exists_discreteSheafificationUnitHom :
∀ {C : Type u} [SmallCategory C]
  (J : GrothendieckTopology C) (hJ : Sheafification J SpaceInfinity.{u}),
  let S := presheafToSheaf J (Type u) ⋙ sheafToPresheaf J (Type u)
  let I := (discretePresheafInclusion C).val
  ∃ η : FunctorHom I (nerveMap S ≫ I),
    (∀ P : Cᵒᵖ ⥤ Type u,
      let h₁ := (discretePresheafInclusion C).property.1 P
      let h₂ : (nerveMap S ≫ I).app _ (nerveVertex P) =
          functorVertex (discretePresheaf (S.obj P)) := by
        exact (congrArg (fun v => I.app _ v) (nerveMap_app_mk₀ S P)).trans
          ((discretePresheafInclusion C).property.1 (S.obj P))
      functorHomEvaluate η (nerveVertex P) =
        eqToHom (congrArg (fun v => HomotopyCategory.mk v) h₁) ≫
          discretePresheafHom (CategoryTheory.toSheafify J P) ≫
          eqToHom (congrArg (fun v => HomotopyCategory.mk v) h₂.symm)) ∧
    IsIso (SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp I (nerveMap S ≫ I) (sheafificationFunctor J hJ) η) := by
  intro C hC J hJ S I
  let η := discreteSheafificationUnitHom J hJ
  refine ⟨η, ?_, discreteSheafificationUnitHom_post_isIso J hJ⟩
  exact discreteSheafificationUnitHom_evaluate J hJ

end SerrePositivity.InfinityCategories.Sheaves
