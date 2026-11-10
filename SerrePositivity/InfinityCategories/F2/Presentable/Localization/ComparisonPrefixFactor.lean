module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.CompactPresentationComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniversePointCoslice
public import SerrePositivity.InfinityCategories.F2.Idempotent.UniverseFullyFaithful

/-!
概要：二表示の全前置比較に、左側の元の表示内の後続因子化を構成する。
方針：前置比較の全データを、元の表示に沿う相対因子化へ渡す。
規約：指定された表示余錐・全前置図式・元の余錐脚を一つの証拠に保持する。
使われ方：HTT 5.5.4.13 の左右交互の後続状態を構成する入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {μ : Cardinal.{u}} {C : SSet.{u + 1}} [Quasicategory C] {I₀ I₁ : SSet.{u}}
  {D₀ : (SSet.uliftFunctor.{u + 1, u}).obj I₀ ⟶ C}
  {D₁ : (SSet.uliftFunctor.{u + 1, u}).obj I₁ ⟶ C}
  {c₀ : JoinCocone D₀} {c₁ : JoinCocone D₁}

/-- 元の左表示の全前置図式の下の図式を、同じ比較図式の前置表示で読む。 -/
def comparisonLeftStages (s : CompactPresentationComparison μ D₀ D₁ c₀ c₁) :
    (SSet.uliftFunctor.{u + 1, u}).obj (sliceUnder s.left_index) ⟶
      sliceUnder ((SSet.uliftFunctor.{u + 1, u}).map s.left_inclusion ≫ s.diagram) :=
  (uliftSliceUnderIso.{u, u + 1} s.left_index).hom ≫
    sliceUnderPostcomp ((SSet.uliftFunctor.{u + 1, u}).map s.left_index) D₀ ≫
      (eqToIso (congrArg sliceUnder s.left_diagram.symm)).hom

/-- 元の左表示余錐を同じ全前置図式の下へ制限した、指定全余錐。 -/
def comparisonLeftCocone (s : CompactPresentationComparison μ D₀ D₁ c₀ c₁) :
    JoinCocone (comparisonLeftStages s) :=
  mapJoinCocone (eqToIso (congrArg sliceUnder s.left_diagram.symm)).hom
    (sourceCosliceRestrictedCocone ((SSet.uliftFunctor.{u + 1, u}).map s.left_index)
      (uliftSliceUnderIso.{u, u + 1} s.left_index).hom D₀ c₀)

/-- 左側の後続因子化は、元の添字内の全余錐と指定比較辺を保持する。 -/
structure ComparisonLeftFactor (s : CompactPresentationComparison μ D₀ D₁ c₀ c₁) where
  index : (sliceUnder s.left_index) _⦋0⦌
  cocone : JoinCocone s.diagram
  edge : (sliceUnder s.diagram).Edge cocone s.augmentation
  prefix_eq : cocone.restrict ((SSet.uliftFunctor.{u + 1, u}).map s.left_inclusion) =
    (comparisonLeftStages s).app _ (ULift.up index)
  projection : (edge.map (sliceUnderRestrict s.diagram
    ((SSet.uliftFunctor.{u + 1, u}).map s.left_inclusion))).edge =
      (Compact.coconeTransportLeg (comparisonLeftCocone s) (ULift.up index)).edge

/-- 元の filtered 左表示から、同じ全前置比較の後続因子化が存在する。 -/
lemma nonempty_comparisonLeftFactor [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    [Quasicategory I₀] [IsKappaFiltered μ I₀]
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (hc₀ : IsColimitCone c₀)
    (s : CompactPresentationComparison μ D₀ D₁ c₀ c₁) : Nonempty (ComparisonLeftFactor s) := by
  have := s.shape_quasicategory
  have := s.left_quasicategory
  have : Mono s.left_inclusion := s.left_mono
  have : Mono ((SSet.uliftFunctor.{u + 1, u}).map s.left_inclusion) :=
    Idempotent.idemUliftMap_mono s.left_inclusion
  obtain ⟨j, w, hw, k, hk⟩ := compactDiagram_factorization_over_terminalPrefixPresentation
    hμ s.shape_small s.left_small s.left_terminal s.left_isTerminal s.left_index hC D₀ c₀ hc₀
    s.diagram s.compact ((SSet.uliftFunctor.{u + 1, u}).map s.left_inclusion)
    s.left_diagram s.augmentation s.left_augmentation
  exact ⟨⟨j, w, k, hw, hk⟩⟩

/-- 左側の後続図式を終域で評価すると、元の同じ左表示の図式になる。 -/
lemma comparisonLeftStages_projection (s : CompactPresentationComparison μ D₀ D₁ c₀ c₁) :
    comparisonLeftStages s ≫ sliceUnderProjection
      ((SSet.uliftFunctor.{u + 1, u}).map s.left_inclusion ≫ s.diagram) =
        (SSet.uliftFunctor.{u + 1, u}).map (sliceUnderProjection s.left_index) ≫ D₀ := by
  let b := (SSet.uliftFunctor.{u + 1, u}).map s.left_index
  let e := eqToIso (congrArg sliceUnder s.left_diagram.symm)
  calc
    _ = (uliftSliceUnderIso.{u, u + 1} s.left_index).hom ≫
        (sliceUnderPostcomp b D₀ ≫ (e.hom ≫ sliceUnderProjection _)) := by
      simp only [comparisonLeftStages, Category.assoc, b, e]
    _ = (uliftSliceUnderIso.{u, u + 1} s.left_index).hom ≫
        (sliceUnderPostcomp b D₀ ≫ sliceUnderProjection (b ≫ D₀)) := by
      rw [cosliceEqIso_projection s.left_diagram.symm]
    _ = (uliftSliceUnderIso.{u, u + 1} s.left_index).hom ≫
        (sliceUnderProjection b ≫ D₀) := by rw [sliceUnderPostcomp_projection]
    _ = ((uliftSliceUnderIso.{u, u + 1} s.left_index).hom ≫ sliceUnderProjection b) ≫ D₀ :=
      (Category.assoc _ _ _).symm
    _ = _ := by rw [uliftSliceUnderIso_projection]

/-- 因子化余錐の頂点は、元の同じ左表示の選んだ後続頂点である。 -/
lemma ComparisonLeftFactor.vertex {s : CompactPresentationComparison μ D₀ D₁ c₀ c₁}
    (f : ComparisonLeftFactor s) :
    f.cocone.vertex = D₀.app _ (ULift.up (JoinCocone.vertex (p := s.left_index) f.index)) := by
  have hv := congrArg JoinCocone.vertex f.prefix_eq
  rw [JoinCocone.vertex_restrict] at hv
  have hp := congrArg
    (fun F : (SSet.uliftFunctor.{u + 1, u}).obj (sliceUnder s.left_index) ⟶ C ↦
      F.app (Opposite.op ⦋0⦌) (ULift.up f.index)) (comparisonLeftStages_projection s)
  change JoinCocone.vertex
    (p := (SSet.uliftFunctor.{u + 1, u}).map s.left_inclusion ≫ s.diagram)
    ((comparisonLeftStages s).app _ (ULift.up f.index)) =
    D₀.app _ (ULift.up (JoinCocone.vertex (p := s.left_index) f.index)) at hp
  exact hv.trans hp

/-- 元の表示の全項が compact なら、後続として選んだ新頂点も同じ濃度で compact。 -/
lemma ComparisonLeftFactor.compact {s : CompactPresentationComparison μ D₀ D₁ c₀ c₁}
    (f : ComparisonLeftFactor s)
    (hD : ∀ i : I₀ _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ (D₀.app _ (ULift.up i))) :
    Compact.IsKappaCompact.{u, u + 1} μ f.cocone.vertex := by
  rw [f.vertex]
  exact hD (JoinCocone.vertex (p := s.left_index) f.index)

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
