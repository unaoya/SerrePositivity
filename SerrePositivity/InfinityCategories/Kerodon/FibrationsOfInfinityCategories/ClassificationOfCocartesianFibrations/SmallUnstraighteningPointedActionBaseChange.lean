module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallUnstraighteningPointedBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallUnstraighteningPointHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraighteningBaseIso

/-!
概要：底を同型で移した指定の小さい unstraightening の射は、pointed 値のホモトピー圏で同じ成分射として作用する。
方針：指定した二つの底変換の同型を通して、元の同じ成分作用を適用する。
使われ方：指定した離散前層の射の密度の脚への作用。
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 底を同型で移した指定の小さい unstraightening の射は、pointed 値のホモトピー圏で同じ成分射として作用する。
Kerodon Remark 5.6.2.18（Tag 0271）の頂点における底変換の法則。 -/
lemma smallUnstraighteningPointedBase_action
    {B D : SSet.{u}} (i : B ≅ D)
    {F G : (SSet.uliftFunctor.{u + 1, u}).obj D ⟶ SpaceInfinity.{u}}
    (a : FunctorHom F G) (b : B _⦋0⦌) :
    let U := SSet.uliftFunctor.{u + 1, u}
    let F' := U.map i.hom ≫ F
    let G' := U.map i.hom ≫ G
    let L := smallLeftUnstraighteningBaseIso i F
    let R := smallLeftUnstraighteningBaseIso i G
    let m := L.hom ≫ smallUnstraighteningFunctorHom a ≫ R.inv
    ∀ hm : m ≫ smallLeftUnstraighteningProjection G' = smallLeftUnstraighteningProjection F',
    ∀ s : (vertexFiber (smallLeftUnstraighteningProjection F') b) _⦋0⦌,
    let t := (vertexFiberMap (smallLeftUnstraighteningProjection F')
      (smallLeftUnstraighteningProjection G') m hm b).app (Opposite.op ⦋0⦌) s
    cosliceFiberPointHom (smallUnstraighteningPointedImage F' b s) ≫
      functorHomEvaluate a (ULift.up (i.hom.app (Opposite.op ⦋0⦌) b)) =
    cosliceFiberPointHom (smallUnstraighteningPointedImage G' b t) := by
  intro U F' G' L R m hm s t
  let d := i.hom.app (Opposite.op ⦋0⦌) b
  let w := smallUnstraighteningFunctorHom a
  let q := smallLeftUnstraighteningProjection F
  let r := smallLeftUnstraighteningProjection G
  let s₀ : (vertexFiber q d) _⦋0⦌ :=
    ⟨L.hom.app (Opposite.op ⦋0⦌) s.val, by
      have h := smallLeftUnstraighteningBaseIso_projection i F
      exact (congrArg (fun k => k.app (Opposite.op ⦋0⦌) s.val) h).trans
        ((congrArg (fun y => i.hom.app (Opposite.op ⦋0⦌) y)
          (s.property.trans (pinchedConstant_zero b))).trans (pinchedConstant_zero d).symm)⟩
  let t₀ := (vertexFiberMap q r w (smallUnstraighteningFunctorHom_projection a) d).app
    (Opposite.op ⦋0⦌) s₀
  let t₁ : (vertexFiber r d) _⦋0⦌ :=
    ⟨R.hom.app (Opposite.op ⦋0⦌) t.val, by
      have h := smallLeftUnstraighteningBaseIso_projection i G
      exact (congrArg (fun k => k.app (Opposite.op ⦋0⦌) t.val) h).trans
        ((congrArg (fun y => i.hom.app (Opposite.op ⦋0⦌) y)
          (t.property.trans (pinchedConstant_zero b))).trans (pinchedConstant_zero d).symm)⟩
  have hS : smallUnstraighteningPointedImage F' b s =
      smallUnstraighteningPointedImage F d s₀ :=
    smallUnstraighteningPointedImage_baseMap i.hom F b s
  have hT : smallUnstraighteningPointedImage G' b t =
      smallUnstraighteningPointedImage G d t₁ :=
    smallUnstraighteningPointedImage_baseMap i.hom G b t
  have hVal : t₁ = t₀ := by
    apply Subtype.ext
    have h : m ≫ R.hom = L.hom ≫ w := by
      dsimp only [m, w]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
    exact congrArg (fun k => k.app (Opposite.op ⦋0⦌) s.val) h
  rw [hS, hT, hVal]
  exact smallUnstraighteningFunctorHom_pointHom a d s₀

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
