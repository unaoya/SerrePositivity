module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsCechConePrism
public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsCechDiagonalIso
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.RelativeBoundaryInvertibility
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluationNaturality

/-!
概要：同じ二つの極限錐を結ぶ指定円柱の頂点辺は可逆。
方針：図式面を元の対角比較に照合し、終点境界の充填で円柱全体の可逆性へ戻す。
  文献対応：HTT 6.2.2.6 と Kerodon Proposition 7.1.6.13（Tag 02XB）。
使われ方：集合値前層の局所同値に沿う切断の可逆性。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open Truncated.HomotopyCategory

open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory

namespace SerrePositivity.InfinityCategories.Sheaves


private lemma iso_of_same_arrow {D : Type*} [Category* D]
    {a b x y : D} {f : a ⟶ b} {g : x ⟶ y}
    (h : Arrow.mk f = Arrow.mk g) (hg : IsIso g) : IsIso f := by
  obtain ⟨rfl, rfl, hh⟩ := (Arrow.mk_eq_mk_iff _ _).mp h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hh
  exact hh.symm ▸ hg

/-- 同じ二つの極限錐を結ぶ指定円柱の頂点辺は可逆。 -/
@[cite HTT "6.2.2.6" (partial := special) "小さい通常の site の集合値 Čech 解消の指定比較。"]
lemma weightedSections_toRange_conePrism_apex_isInvertible :
∀ {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E],
∀ (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ Type u} (f : P ⟶ Q)
 [CategoryTheory.Presheaf.IsLocallyInjective J f]
 (O : Presheaf C E) (hO : IsSheaf J O) (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E),
let g := Subfunctor.toRange f
let A := mapJoinCone (weightedSections O hE)
 (coconeReverseCone (discretePresheafCocone (relativeCechCocone g)))
∀ (d : JoinCone (SSet.const ((weightedSections O hE).app _
 (opObjEquiv.symm (functorVertex (discretePresheaf P)))) : cechReverseIndex.{u} ⟶ E))
 (hd : IsLimitCone d)
 (H : join (Δ[0] : SSet.{u + 1}) cechReverseIndex.{u} ⊗ Δ[1] ⟶ E)
 (ρ : SSet.Homotopy (SSet.yonedaEquiv.symm A.vertex) (SSet.yonedaEquiv.symm d.vertex))
 (h₀ : SSet.ι₀ ≫ H = A.val) (h₁ : SSet.ι₁ ≫ H = d.val)
 (hD : (joinInr (Δ[0] : SSet.{u + 1}) cechReverseIndex.{u} ▷ Δ[1]) ≫ H =
   (functorHomHomotopy (weightedSections_relativeCechDiagonalHom g O hE)).h)
 (hV : (joinInl (Δ[0] : SSet.{u + 1}) cechReverseIndex.{u} ▷ Δ[1]) ≫ H = ρ.h),
 IsInvertibleEdge
   (simplicialHomotopyVertexEdge ρ (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌))).toTruncated := by
  intro C hC E hQC J P Q f hf O hO hE g A d hd H ρ h₀ h₁ hD hV
  let K := cechReverseIndex.{u}
  let T : SSet.Homotopy A.val d.val := {
    h := H
    h₀ := h₀
    h₁ := h₁
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      exact False.elim a.1.property }
  let a := functorEdgeOfSimplicialHomotopy T
  let m := homMk a
  let pr := coneRestriction K E
  let θ := weightedSections_relativeCechDiagonalHom g O hE
  let t := functorHomHomotopy θ
  let i := joinInr (Δ[0] : SSet.{u + 1}) K
  let s := functorHomotopyPrecomp T i
  have hs : s.h = t.h := hD
  have hs1 : Arrow.mk (homMk (functorEdgeOfSimplicialHomotopy s)) =
      Arrow.mk (homMk (functorEdgeOfSimplicialHomotopy t)) := by
    apply congr_arrowMk_homMk
    exact congrArg (fun k : K ⊗ Δ[1] ⟶ E => SSet.yonedaEquiv (curry k)) hs
  have hp : Arrow.mk ((hoFunctor.map pr).toFunctor.map m) = Arrow.mk θ :=
    (congrArg Arrow.mk (functorHomotopyPrecomp_hom T i).symm).trans
      (hs1.trans (congrArg Arrow.mk (functorHomHomotopy_hom θ)))
  letI : CategoryTheory.Presheaf.IsLocallyInjective J g := toRange_isLocallyInjective J f
  have hi : IsIso θ := weightedSections_relativeCechDiagonalHom_isIso J g O hO hE
  have hp' : IsIso ((hoFunctor.map pr).toFunctor.map m) := iso_of_same_arrow hp hi
  letI : IsIso m := isInvertibleEdge_of_terminalBoundaries pr a
    (terminalBoundaryLifting_coneRestriction_of_isLimitCone A
      (weightedSections_rangeCech_isLimit f O hE))
    (terminalBoundaryLifting_coneRestriction_of_isLimitCone d hd) hp'
  let v := stdSimplex.objEquiv.symm (𝟙 ⦋0⦌)
  let j := joinInl (Δ[0] : SSet.{u + 1}) K
  let x := j.app (Opposite.op ⦋0⦌) v
  have hEval : IsIso (functorHomEvaluate m x) := inferInstance
  rw [functorHomEvaluate_homotopy] at hEval
  apply iso_of_same_arrow _ hEval
  apply congr_arrowMk_homMk
  have he := homotopyVertexEdge_precomp j T v
  let w := ((Truncated.Edge.id (X := (truncation 2).obj (Δ[0] : SSet.{u + 1})) v).edge,
    homotopyIntervalEdge.edge)
  change ((j ▷ Δ[1]) ≫ H).app (Opposite.op ⦋1⦌) w =
    (simplicialHomotopyVertexEdge T x).edge at he
  rw [hV] at he
  exact he

end SerrePositivity.InfinityCategories.Sheaves
