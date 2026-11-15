module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorDoubleConeAugmentationComparison
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeSource
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomotopyClasses
public import Mathlib.CategoryTheory.Comma.Arrow

/-!
概要：元の全 cone の同じ指定源への像を元の全 augmentation 同型の逆へ照合する。
方針：同じ実円柱の Arrow 比較と全三角形の後合成、逆の一意性を使う。
規約：HA Construction 1.3.1.13・§1.3.4、元の全族と同じ実分解。
使われ方：元の全評価屋根と元の K の Hom 誘導射の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.Modules
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

private lemma postcompTriangle {K S T : SSet.{u + 1}} {U V : K ⟶ S}
    (F : S ⟶ T) (l : SSet.Homotopy U V) (r : SSet.Homotopy V U)
    (h : Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy l) ≫
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy r) = 𝟙 _) :
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy (functorHomotopyPostcomp l F)) ≫
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy (functorHomotopyPostcomp r F)) = 𝟙 _ := by
  let Φ := (hoFunctor.map ((ihom K).map F)).toFunctor
  have hh := congrArg Φ.map h
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at hh
  rw [← functorHomotopyPostcomp_hom, ← functorHomotopyPostcomp_hom] at hh
  exact hh

private lemma inverseArrowEq {C : Type*} [Category* C] {x y x' y' : C}
    (f : x ⟶ y) (g : x' ⟶ y') [IsIso f] [IsIso g] (h : Arrow.mk f = Arrow.mk g) :
    Arrow.mk (inv f) = Arrow.mk (inv g) := by
  obtain ⟨hx, hy, hh⟩ := (Arrow.mk_eq_mk_iff f g).mp h
  cases hx
  cases hy
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hh
  cases hh
  rfl

private lemma isIsoOfArrowEq {C : Type*} [Category* C] {x y x' y' : C}
    (f : x ⟶ y) (g : x' ⟶ y') [IsIso g] (h : Arrow.mk f = Arrow.mk g) : IsIso f := by
  have hg : IsIso (Arrow.mk g).hom := by
    change IsIso g
    infer_instance
  exact (congrArg (fun a : Arrow C => IsIso a.hom) h).mpr hg

private lemma leftInverse_eq_inv {C : Type*} [Category* C] {x y : C}
    (c : x ⟶ y) (e : y ⟶ x) [IsIso e] (h : c ≫ e = 𝟙 x) : c = inv e := by
  calc
    c = c ≫ (e ≫ inv e) := by rw [IsIso.hom_inv_id, Category.comp_id]
    _ = (c ≫ e) ≫ inv e := (Category.assoc _ _ _).symm
    _ = inv e := by rw [h, Category.id_comp]

lemma strictRawModuleTensorDoubleConeSliceEvaluation_source_arrow :
    Arrow.mk (Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (functorHomotopyPostcomp
        (strictRawModuleTensorDoubleConeSliceEvaluationHomotopy A X P Q)
        (moduleResolution A (dgAlgebraCategory A ((assocForget A).obj X)))))) =
    Arrow.mk (strictRawModuleTensorElementSourceAugmentationIso A X P Q).hom := by
  change Arrow.mk (Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (functorHomotopyPostcomp
        (strictRawModuleTensorDoubleConeSliceEvaluationHomotopy A X P Q)
        (moduleResolution A (dgAlgebraCategory A ((assocForget A).obj X)))))) =
    Arrow.mk (Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (strictRawModuleDiagramNatTransHomotopy A X
        (strictRawModuleTensorElementAugmentation A X P Q))))
  apply functorHomotopy_hom_arrow_of_h_eq
  exact strictRawModuleTensorDoubleConeSliceEvaluationHomotopy_h_source A X P Q

lemma strictRawModuleTensorConePostSource_inverse_arrow :
    Arrow.mk (Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (functorHomotopyPostcomp
        (strictRawModuleTensorConeHomotopy A X P Q)
        (moduleResolution A (dgAlgebraCategory A ((assocForget A).obj X)))))) =
    Arrow.mk (strictRawModuleTensorElementSourceAugmentationIso A X P Q).inv := by
  let F := moduleResolution A (dgAlgebraCategory A ((assocForget A).obj X))
  let c := Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
    (functorHomotopyPostcomp (strictRawModuleTensorConeHomotopy A X P Q) F))
  let e := Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
    (functorHomotopyPostcomp (strictRawModuleTensorDoubleConeSliceEvaluationHomotopy A X P Q) F))
  have he : Arrow.mk e = Arrow.mk (strictRawModuleTensorElementSourceAugmentationIso A X P Q).hom :=
    strictRawModuleTensorDoubleConeSliceEvaluation_source_arrow A X P Q
  letI : IsIso e := isIsoOfArrowEq e _ he
  have ht : c ≫ e = 𝟙 _ := postcompTriangle F
    (strictRawModuleTensorConeHomotopy A X P Q)
    (strictRawModuleTensorDoubleConeSliceEvaluationHomotopy A X P Q)
    (strictRawModuleTensorDoubleConeSliceEvaluation_triangle A X P Q)
  exact (congrArg Arrow.mk (leftInverse_eq_inv c e ht)).trans
    (inverseArrowEq e (strictRawModuleTensorElementSourceAugmentationIso A X P Q).hom he)

lemma strictRawModuleTensorConeSourceFamilyHom_inverse_arrow :
    Arrow.mk (strictRawModuleTensorConeSourceFamilyHom A X P Q) =
      Arrow.mk (strictRawModuleTensorElementSourceAugmentationIso A X P Q).inv := by
  have h := functorHomotopy_hom_arrow_of_h_eq
    (strictRawModuleTensorConeSourceHomotopy A X P Q)
    (functorHomotopyPostcomp (strictRawModuleTensorConeHomotopy A X P Q)
      (moduleResolution A (dgAlgebraCategory A ((assocForget A).obj X))))
    (strictRawModuleTensorConeSourceHomotopy_h A X P Q)
  exact h.trans (strictRawModuleTensorConePostSource_inverse_arrow A X P Q)

lemma strictRawModuleTensorConeSourceFamilyHom_isIso :
    IsIso (strictRawModuleTensorConeSourceFamilyHom A X P Q) :=
  isIsoOfArrowEq _ _ (strictRawModuleTensorConeSourceFamilyHom_inverse_arrow A X P Q)

end SerrePositivity.EInfinity.BarrattEccles
