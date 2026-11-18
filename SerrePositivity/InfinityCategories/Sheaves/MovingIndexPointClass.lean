module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.RightKanIntervalCosliceComposition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Definition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceEdgeFamilies
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.FaithfulNerveReadout
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PointCoslicePostIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RelativeFunctorPostEquivalence
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeFunctorIsPullbackIso
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.ExtOne
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.CosliceHomotopy

/-!
概要：区間の終点脚の切断と元の始点脚を、同じ右 Kan 図式の上で比較する。
方針：指定した辺と添字の座標に既存の評価則を適用する。
使われ方：離散前層の重み付き切断の自然性。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
set_option autoImplicit false
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Sheaves
open SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

namespace SerrePositivity.InfinityCategories.Sheaves

def rightKanMovingIndexFace
    {J K X : SSet.{u}} (δ : K ⟶ X)
    {v₀ v₁ : X _⦋0⦌} (e : (Δ[1] : SSet.{u}) ⟶ X)
    (he₀ : stdSimplex.δ (1 : Fin 2) ≫ e = SSet.yonedaEquiv.symm v₀)
    (he₁ : stdSimplex.δ (0 : Fin 2) ≫ e = SSet.yonedaEquiv.symm v₁)
    (j₀ : J ⟶ rightKanShape δ v₀) (j₁ : J ⟶ rightKanShape δ v₁) : Prop :=
  let q₀ := sliceUnderProjection (SSet.yonedaEquiv.symm v₀)
  let q₁ := sliceUnderProjection (SSet.yonedaEquiv.symm v₁)
  let a₀ := j₀ ≫ pullback.fst q₀ δ
  let a₁ := j₁ ≫ pullback.fst q₁ δ
  let p := (j₀ ≫ rightKanProjection δ v₀) ≫ δ
  let r₀ := sliceUnderRestrict e (stdSimplex.δ (1 : Fin 2)) ≫
    eqToHom (congrArg sliceUnder he₀)
  let r₁ := sliceUnderRestrict e (stdSimplex.δ (0 : Fin 2)) ≫
    eqToHom (congrArg sliceUnder he₁)
  ∃ (w : J ⟶ sliceUnder e)
    (h₀ : (w ≫ r₀) ≫ q₀ = p)
    (h₁ : a₀ ≫ q₀ = p),
    w ≫ r₁ = a₁ ∧
      Nonempty (VertexIso (relativeFunctorVertex q₀ p (w ≫ r₀) h₀)
        (relativeFunctorVertex q₀ p a₀ h₁))

theorem rightKanMovingIndex_target_section
    {J K X : SSet.{u}} [Quasicategory X] (δ : K ⟶ X)
    {v₀ v₁ : X _⦋0⦌} (e : (Δ[1] : SSet.{u}) ⟶ X)
    (he₀ : stdSimplex.δ (1 : Fin 2) ≫ e = SSet.yonedaEquiv.symm v₀)
    (he₁ : stdSimplex.δ (0 : Fin 2) ≫ e = SSet.yonedaEquiv.symm v₁)
    (j₀ : J ⟶ rightKanShape δ v₀) (j₁ : J ⟶ rightKanShape δ v₁)
    (hj : j₀ ≫ rightKanProjection δ v₀ = j₁ ≫ rightKanProjection δ v₁) :
    let q₀ := sliceUnderProjection (SSet.yonedaEquiv.symm v₀)
    let q₁ := sliceUnderProjection (SSet.yonedaEquiv.symm v₁)
    let a₀ := j₀ ≫ pullback.fst q₀ δ
    let a₁ := j₁ ≫ pullback.fst q₁ δ
    let p := (j₀ ≫ rightKanProjection δ v₀) ≫ δ
    let r₀ := sliceUnderRestrict e (stdSimplex.δ (1 : Fin 2)) ≫
      eqToHom (congrArg sliceUnder he₀)
    let r₁ := sliceUnderRestrict e (stdSimplex.δ (0 : Fin 2)) ≫
      eqToHom (congrArg sliceUnder he₁)
    let w := a₁ ≫ (eqToHom (congrArg sliceUnder he₁.symm) ≫ cosliceEdgeSection e)
    w ≫ r₁ = a₁ ∧ (w ≫ r₀) ≫ q₀ = p ∧ a₀ ≫ q₀ = p := by
  intro q₀ q₁ a₀ a₁ p r₀ r₁ w
  let s₁ := eqToHom (congrArg sliceUnder he₁.symm) ≫ cosliceEdgeSection e
  have h₁ : s₁ ≫ r₁ = 𝟙 _ := by
    dsimp only [s₁, r₁]
    simp only [Category.assoc]
    rw [← Category.assoc (cosliceEdgeSection e), cosliceEdgeSection_target,
      Category.id_comp, eqToHom_trans, eqToHom_refl]
  have hnorm (x : Δ[0] ⟶ X) (i : Δ[0] ⟶ Δ[1]) (h : i ≫ e = x) :
      (sliceUnderRestrict e i ≫ eqToHom (congrArg sliceUnder h)) ≫ sliceUnderProjection x =
        sliceUnderProjection e := by
    subst x
    simp only [eqToHom_refl, Category.comp_id]
    exact sliceUnderRestrict_projection e i
  have hr₀ : r₀ ≫ q₀ = sliceUnderProjection e := hnorm _ _ he₀
  have hr₁ : r₁ ≫ q₁ = sliceUnderProjection e := hnorm _ _ he₁
  have hpa₀ : a₀ ≫ q₀ = p := by
    change (j₀ ≫ pullback.fst q₀ δ) ≫ q₀ = (j₀ ≫ pullback.snd q₀ δ) ≫ δ
    simp only [Category.assoc, pullback.condition]
  have hpa₁ : a₁ ≫ q₁ = p := by
    change (j₁ ≫ pullback.fst q₁ δ) ≫ q₁ = (j₀ ≫ pullback.snd q₀ δ) ≫ δ
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (fun k => k ≫ δ) hj.symm
  change (a₁ ≫ s₁) ≫ r₁ = a₁ ∧ ((a₁ ≫ s₁) ≫ r₀) ≫ q₀ = p ∧ a₀ ≫ q₀ = p
  refine ⟨?_, ?_, hpa₀⟩
  · rw [Category.assoc, h₁, Category.comp_id]
  · rw [Category.assoc (a₁ ≫ s₁), hr₀, ← hr₁, ← Category.assoc (a₁ ≫ s₁),
      Category.assoc a₁, h₁, Category.comp_id, hpa₁]

def rightKanMovingIndex_selectedSource
    {J K X : SSet.{u}} [Quasicategory X] (δ : K ⟶ X)
    {v₀ v₁ : X _⦋0⦌} (e : (Δ[1] : SSet.{u}) ⟶ X)
    (he₀ : stdSimplex.δ (1 : Fin 2) ≫ e = SSet.yonedaEquiv.symm v₀)
    (he₁ : stdSimplex.δ (0 : Fin 2) ≫ e = SSet.yonedaEquiv.symm v₁)
    (j₀ : J ⟶ rightKanShape δ v₀) (j₁ : J ⟶ rightKanShape δ v₁)
    (hj : j₀ ≫ rightKanProjection δ v₀ = j₁ ≫ rightKanProjection δ v₁) : Prop :=
  let q₀ := sliceUnderProjection (SSet.yonedaEquiv.symm v₀)
  let a₀ := j₀ ≫ pullback.fst q₀ δ
  let p := (j₀ ≫ rightKanProjection δ v₀) ≫ δ
  let r₀ := sliceUnderRestrict e (stdSimplex.δ (1 : Fin 2)) ≫
    eqToHom (congrArg sliceUnder he₀)
  let hw := rightKanMovingIndex_target_section δ e he₀ he₁ j₀ j₁ hj
  let w := (j₁ ≫ pullback.fst (sliceUnderProjection (SSet.yonedaEquiv.symm v₁)) δ) ≫
    (eqToHom (congrArg sliceUnder he₁.symm) ≫ cosliceEdgeSection e)
  Nonempty (VertexIso (relativeFunctorVertex q₀ p (w ≫ r₀) hw.2.1)
    (relativeFunctorVertex q₀ p a₀ hw.2.2))

theorem rightKanMovingIndexFace_of_selectedSource
    {J K X : SSet.{u}} [Quasicategory X] (δ : K ⟶ X)
    {v₀ v₁ : X _⦋0⦌} (e : (Δ[1] : SSet.{u}) ⟶ X)
    (he₀ : stdSimplex.δ (1 : Fin 2) ≫ e = SSet.yonedaEquiv.symm v₀)
    (he₁ : stdSimplex.δ (0 : Fin 2) ≫ e = SSet.yonedaEquiv.symm v₁)
    (j₀ : J ⟶ rightKanShape δ v₀) (j₁ : J ⟶ rightKanShape δ v₁)
    (hj : j₀ ≫ rightKanProjection δ v₀ = j₁ ≫ rightKanProjection δ v₁)
    (hsource : rightKanMovingIndex_selectedSource δ e he₀ he₁ j₀ j₁ hj) :
    rightKanMovingIndexFace δ e he₀ he₁ j₀ j₁ := by
  let hw := rightKanMovingIndex_target_section δ e he₀ he₁ j₀ j₁ hj
  exact ⟨_, hw.2.1, hw.2.2, hw.1, hsource⟩

theorem rightKanMovingIndex_selectedSource_of_nerve_readout
    {J K X : SSet.{u}} [Quasicategory K] [Quasicategory X]
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (p : C ⥤ D) [p.Faithful] (r : nerve C ⟶ K) [LeftFibration r]
    (s : K ⟶ nerve D) (hs : r ≫ s = nerveMap p)
    (δ : K ⟶ X) {v₀ v₁ : X _⦋0⦌} (e : (Δ[1] : SSet.{u}) ⟶ X)
    (he₀ : stdSimplex.δ (1 : Fin 2) ≫ e = SSet.yonedaEquiv.symm v₀)
    (he₁ : stdSimplex.δ (0 : Fin 2) ≫ e = SSet.yonedaEquiv.symm v₁)
    (j₀ : J ⟶ rightKanShape δ v₀) (j₁ : J ⟶ rightKanShape δ v₁)
    (hj : j₀ ≫ rightKanProjection δ v₀ = j₁ ≫ rightKanProjection δ v₁)
    (i : rightKanShape δ v₀ ⟶ nerve C) (hi : i ≫ r = rightKanProjection δ v₀)
    (ei : IsPrecompositionEquivalence i) :
    let q₀ := sliceUnderProjection (SSet.yonedaEquiv.symm v₀)
    let a₀ := j₀ ≫ pullback.fst q₀ δ
    let k := j₀ ≫ rightKanProjection δ v₀
    let r₀ := sliceUnderRestrict e (stdSimplex.δ (1 : Fin 2)) ≫
      eqToHom (congrArg sliceUnder he₀)
    let hw := rightKanMovingIndex_target_section δ e he₀ he₁ j₀ j₁ hj
    let w := (j₁ ≫ pullback.fst (sliceUnderProjection (SSet.yonedaEquiv.symm v₁)) δ) ≫
      (eqToHom (congrArg sliceUnder he₁.symm) ≫ cosliceEdgeSection e)
    (∀ x : J _⦋0⦌,
      (pullback.lift (w ≫ r₀) k hw.2.1 ≫ i).app _ x = (j₀ ≫ i).app _ x) →
    rightKanMovingIndex_selectedSource δ e he₀ he₁ j₀ j₁ hj := by
  intro q₀ a₀ k r₀ hw w hv
  have h₀ : pullback.lift a₀ k hw.2.2 = j₀ := by
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact pullback.lift_snd _ _ _
  have hRight : ∀ x : J _⦋0⦌,
      (pullback.lift (w ≫ r₀) k hw.2.1 ≫ i).app _ x =
        (pullback.lift a₀ k hw.2.2 ≫ i).app _ x := by
    rw [h₀]
    exact hv
  exact relativeFunctorIso_of_pullback_nerve_readout p r s hs δ q₀ k i hi ei
    (w ≫ r₀) a₀ hw.2.1 hw.2.2 hRight

private lemma cosliceIntervalNormalized_source_eq_of_comp
    {X : SSet.{u}} {a b : X _⦋0⦌} (e : X.Edge a b)
    (c : JoinCocone (SSet.yonedaEquiv.symm e.edge)) :
    let η := SSet.yonedaEquiv.symm e.edge
    let he₀ := e.δ_one_yonedaEquiv_symm
    let he₁ := e.δ_zero_yonedaEquiv_symm
    let r₀ := sliceUnderRestrict η (stdSimplex.δ (1 : Fin 2)) ≫ eqToHom (congrArg sliceUnder he₀)
    let r₁ := sliceUnderRestrict η (stdSimplex.δ (0 : Fin 2)) ≫ eqToHom (congrArg sliceUnder he₁)
    ∀ (v : X _⦋0⦌), c.vertex = v →
    ∀ (s₀ t₀ : (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm a)) v) _⦋0⦌)
      (s₁ : (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm b)) v) _⦋0⦌),
    s₀.val = r₀.app (Opposite.op ⦋0⦌) c →
    s₁.val = r₁.app (Opposite.op ⦋0⦌) c →
    Truncated.HomotopyCategory.homMk e.toTruncated ≫
      Truncated.HomotopyCategory.homMk (normalizedCosliceFiberEdge b v s₁) =
        Truncated.HomotopyCategory.homMk (normalizedCosliceFiberEdge a v t₀) →
    Truncated.HomotopyCategory.homMk (cosliceFiberEdge _ _ s₀) =
      Truncated.HomotopyCategory.homMk (cosliceFiberEdge _ _ t₀) := by
  intro η h₀ h₁ r₀ r₁ v hv s₀ t₀ s₁ hs ht hg
  subst v
  have H := (cosliceIntervalNormalized_homMk e c s₀ s₁ hs ht).symm.trans hg
  let v := c.vertex
  let ya : X _⦋0⦌ := SSet.yonedaEquiv (SSet.yonedaEquiv.symm a)
  let f : Truncated.Edge (X := (truncation 2).obj X) ya v := cosliceFiberEdge _ _ s₀
  let g : Truncated.Edge (X := (truncation 2).obj X) ya v := cosliceFiberEdge _ _ t₀
  have hya : ya = a := SSet.yonedaEquiv.apply_symm_apply a
  have key : ∀ (z : X _⦋0⦌) (hz : ya = z),
      let f' : Truncated.Edge (X := (truncation 2).obj X) z v :=
        ⟨f.edge, f.src_eq.trans hz, f.tgt_eq⟩
      let g' : Truncated.Edge (X := (truncation 2).obj X) z v :=
        ⟨g.edge, g.src_eq.trans hz, g.tgt_eq⟩
      Truncated.HomotopyCategory.homMk f' = Truncated.HomotopyCategory.homMk g' →
      Truncated.HomotopyCategory.homMk f = Truncated.HomotopyCategory.homMk g := by
    intro z hz
    subst z
    exact id
  exact key a hya H

private theorem normalizedCosliceSource_eq_of_terminalLeg
    {X : SSet.{u}} {a b v : X _⦋0⦌}
    (e : X.Edge a b) (c : JoinCocone (SSet.yonedaEquiv.symm e.edge)) :
    let η := SSet.yonedaEquiv.symm e.edge
    let q₀ := sliceUnderProjection (SSet.yonedaEquiv.symm a)
    let q₁ := sliceUnderProjection (SSet.yonedaEquiv.symm b)
    let r₀ := sliceUnderRestrict η (stdSimplex.δ (1 : Fin 2)) ≫
      eqToHom (congrArg sliceUnder e.δ_one_yonedaEquiv_symm)
    let r₁ := sliceUnderRestrict η (stdSimplex.δ (0 : Fin 2)) ≫
      eqToHom (congrArg sliceUnder e.δ_zero_yonedaEquiv_symm)
    ∀ (f g : (vertexFiber q₀ v) _⦋0⦌) (z : (sliceUnder (SSet.yonedaEquiv.symm b)) _⦋0⦌),
    f.val = r₀.app (Opposite.op ⦋0⦌) c →
    r₁.app (Opposite.op ⦋0⦌) c = z →
    (∀ h : (vertexFiber q₁ v) _⦋0⦌, h.val = z →
      Truncated.HomotopyCategory.homMk e.toTruncated ≫
        Truncated.HomotopyCategory.homMk (normalizedCosliceFiberEdge b v h) =
          Truncated.HomotopyCategory.homMk (normalizedCosliceFiberEdge a v g)) →
    Truncated.HomotopyCategory.homMk (cosliceFiberEdge _ _ f) =
      Truncated.HomotopyCategory.homMk (cosliceFiberEdge _ _ g) := by
  intro η q₀ q₁ r₀ r₁ f g z hf hz H
  have hr₀ : r₀ ≫ q₀ = sliceUnderProjection η := by
    dsimp only [r₀, q₀]
    rw [Category.assoc, sliceUnder_eqToHom_projection e.δ_one_yonedaEquiv_symm,
      sliceUnderRestrict_projection]
  have hr₁ : r₁ ≫ q₁ = sliceUnderProjection η := by
    dsimp only [r₁, q₁]
    rw [Category.assoc, sliceUnder_eqToHom_projection e.δ_zero_yonedaEquiv_symm,
      sliceUnderRestrict_projection]
  have hv : c.vertex = v := by
    have h := congrArg (fun a => a.app (Opposite.op ⦋0⦌) c) hr₀
    exact h.symm.trans (by
      change q₀.app _ (r₀.app _ c) = v
      rw [← hf]
      exact f.property.trans (pinchedConstant_zero _))
  let y : (vertexFiber q₁ v) _⦋0⦌ := ⟨r₁.app _ c, by
    rw [pinchedConstant_zero]
    exact (congrArg (fun a => a.app (Opposite.op ⦋0⦌) c) hr₁).trans hv⟩
  exact cosliceIntervalNormalized_source_eq_of_comp e c v hv f g y hf rfl (H y hz)

/-- 区間の終点脚の切断と元の始点脚を、同じ右 Kan 図式の上で比較する。
Kerodon §4.6 の slice と join、§7.3（Tag 02Y9）。HTT 5.1.5.6 の局所比較の境界計算。 -/
@[cite HTT "5.1.5.6" (partial := component)
  "指定右 Kan 比較に用いる、区間の端点への制限と添字の局所的な照合。"]
lemma rightKanMovingIndex_pointComp_of_projectedLegs
    {J K X : SSet.{u}} [Quasicategory X] (δ : K ⟶ X)
    {v₀ v₁ : X _⦋0⦌} (e : X.Edge v₀ v₁)
    (j₀ : J ⟶ rightKanShape δ v₀) (j₁ : J ⟶ rightKanShape δ v₁)
    (hj : j₀ ≫ rightKanProjection δ v₀ = j₁ ≫ rightKanProjection δ v₁) :
    let η := SSet.yonedaEquiv.symm e.edge
    let q₀ := sliceUnderProjection (SSet.yonedaEquiv.symm v₀)
    let q₁ := sliceUnderProjection (SSet.yonedaEquiv.symm v₁)
    let a₀ := j₀ ≫ pullback.fst q₀ δ
    let a₁ := j₁ ≫ pullback.fst q₁ δ
    (∀ (d : J _⦋0⦌) (y : X _⦋0⦌)
      (g : (vertexFiber q₀ y) _⦋0⦌) (h : (vertexFiber q₁ y) _⦋0⦌),
      g.val = a₀.app _ d → h.val = a₁.app _ d →
      Truncated.HomotopyCategory.homMk e.toTruncated ≫
        Truncated.HomotopyCategory.homMk (normalizedCosliceFiberEdge v₁ y h) =
          Truncated.HomotopyCategory.homMk (normalizedCosliceFiberEdge v₀ y g)) →
    ∀ (he₀ : stdSimplex.δ (1 : Fin 2) ≫ η = SSet.yonedaEquiv.symm v₀)
      (he₁ : stdSimplex.δ (0 : Fin 2) ≫ η = SSet.yonedaEquiv.symm v₁),
    let k := j₀ ≫ rightKanProjection δ v₀
    let r₀ := sliceUnderRestrict η (stdSimplex.δ (1 : Fin 2)) ≫ eqToHom (congrArg sliceUnder he₀)
    let hw := rightKanMovingIndex_target_section δ η he₀ he₁ j₀ j₁ hj
    let w := a₁ ≫ (eqToHom (congrArg sliceUnder he₁.symm) ≫ cosliceEdgeSection η)
    ∀ d : J _⦋0⦌,
    let l := pullback.lift (w ≫ r₀) k hw.2.1
    let xx := l.app (Opposite.op ⦋0⦌) d
    let zz := (rightKanProjection δ v₀).app (Opposite.op ⦋0⦌) xx
    ∀ (f g : (vertexFiber q₀ (δ.app _ zz)) _⦋0⦌),
    f.val = (pullback.fst q₀ δ).app _ xx → g.val = a₀.app _ d →
    Truncated.HomotopyCategory.homMk (cosliceFiberEdge _ _ f) =
      Truncated.HomotopyCategory.homMk (cosliceFiberEdge _ _ g) := by
  intro η q₀ q₁ a₀ a₁ H he₀ he₁ k r₀ hw w d l xx zz f g hf hg
  let c : JoinCocone η := w.app (Opposite.op ⦋0⦌) d
  have hf' : f.val = r₀.app (Opposite.op ⦋0⦌) c := by
    refine hf.trans ?_
    change (l ≫ pullback.fst q₀ δ).app (Opposite.op ⦋0⦌) d = _
    exact congrArg (fun a => a.app (Opposite.op ⦋0⦌) d) (pullback.lift_fst (w ≫ r₀) k hw.2.1)
  apply normalizedCosliceSource_eq_of_terminalLeg e c f g (a₁.app _ d) hf'
  · exact congrArg (fun a => a.app (Opposite.op ⦋0⦌) d) hw.1
  · intro h hh
    exact H d (δ.app _ zz) g h hg hh

end SerrePositivity.InfinityCategories.Sheaves
