module
public import SerrePositivity.KST.ProExcision.RelativeModuleIso
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels

/-!
# 実相対加群の図式と余核の普遍性

概要：実加群図式の自然変換の像による商を実図式にし、その射影が実余核であることを示す。
方針：既存の実商写像を束ね、各評価で通常の商の普遍性を使う。
規約：KST Appendix A、Proposition 4.14。使われ方：相対商と rank 余極限の交換。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u r v w
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Limits
variable {R : Type r} [Ring R] {J : Type v} [Category.{w} J]
variable {A B : J ⥤ ModuleCat.{u} R}

/-- 概要：自然変換の各成分の実像による商からなる実加群図式。
方針：自然性の実正方形に既存の実相対商写像を適用する。
規約：KST Proposition 4.14。使われ方：有限 rank の相対項の余極限。 -/
def relativeModuleDiagram (f : A ⟶ B) : J ⥤ ModuleCat.{u} R where
  obj j := relativeModule (f.app j)
  map {i j} φ := relativeModuleMap _ _ (A.map φ) (B.map φ) (f.naturality φ).symm
  map_id j := by
    simp only [A.map_id, B.map_id, relativeModuleMap_id]
  map_comp φ ψ := by
    rw [relativeModuleMap_comp]
    apply relativeModuleMap_eq_of_right_eq
    exact B.map_comp φ ψ

/-- 概要：実加群図式から像の商図式への実射影。
方針：各次数で通常の商の射影を用い、実商写像の定義で自然性を示す。
規約：KST App. A。使われ方：相対図式の余核の普遍性。 -/
def relativeModuleDiagramProjection (f : A ⟶ B) : B ⟶ relativeModuleDiagram f where
  app j := ModuleCat.ofHom (f.app j).hom.range.mkQ
  naturality {i j} φ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- 概要：実自然変換と実相対商射影の合成は零。
方針：各成分で像の元が商で零になることを使う。
規約：KST App. A。使われ方：実余核余錐の条件。 -/
lemma relativeModuleDiagramProjection_condition (f : A ⟶ B) :
    f ≫ relativeModuleDiagramProjection f = 0 := by
  apply NatTrans.ext
  funext j
  exact ModuleCat.hom_ext (LinearMap.range_mkQ_comp (f.app j).hom)

/-- 概要：実相対商図式の標準余核余錐。
方針：実射影と実零合成をまとめる。
規約：KST Proposition 4.14。使われ方：余極限関手に写す実余錐。 -/
def relativeModuleDiagramCofork (f : A ⟶ B) : CokernelCofork f :=
  CokernelCofork.ofπ (relativeModuleDiagramProjection f) (relativeModuleDiagramProjection_condition f)

/-- 概要：実相対商図式は自然変換の実余核。
方針：各評価で通常の実商の余核の普遍性を使い、評価の共同反映性で戻す。
規約：KST App. A、Proposition 4.14。使われ方：実相対商と順序余極限の交換。 -/
def relativeModuleDiagramIsCokernel (f : A ⟶ B) : IsColimit (relativeModuleDiagramCofork f) :=
  evaluationJointlyReflectsColimits _ (fun j ↦
    ((relativeModuleDiagramCofork f).isColimitMapCoconeEquiv
      ((evaluation J (ModuleCat.{u} R)).obj j)).symm
        (ModuleCat.cokernelIsColimit (f.app j)))

end SerrePositivity.KST.ProExcision
