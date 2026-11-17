module

public import SerrePositivity.AlgebraicGeometry.PairedCechGeometryMaps
public import SerrePositivity.AlgebraicGeometry.SchemeCechTupleAffine
public import SerrePositivity.AlgebraicGeometry.SchemeCommonAffineCover
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
概要：二つの増大 nerve の元のタプル開は、反変な射に沿い、全ての次数でアフィン被覆となる。
方針：元のタプル開の包含を二つの射影で引き戻し、増大点は全開集合を使う。
規約：同じ位置写像・実際の積・被覆の開集合を保持する。
使われ方：二変数の Čech 係数と局所切断の比較（計画 P12・P19）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
set_option backward.isDefEq.respectTransparency false

/-- 元の二つのタプルの位置写像による開は、同じ幾何的な射の逆像に含まれる。 -/
theorem pairedCechOpen_map_le {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (h : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    {a a' b b' : AugmentedSimplexCategory} (α : a ⟶ a') (β : b ⟶ b')
    (t : (Fin (augmentedTupleLength a') → ι) × (Fin (augmentedTupleLength b') → κ)) :
    pairedCechOpen h g U V a' b' t ≤ pairedCechSchemeMap h g α β ⁻¹ᵁ
      pairedCechOpen h g U V a b
        (t.1 ∘ augmentedTupleIndexMap α, t.2 ∘ augmentedTupleIndexMap β) := by
  let H := AugmentedSimplexCategory.equivAugmentedSimplicialObject.inverse.obj
    (Arrow.mk h).augmentedCechNerve
  let G := AugmentedSimplexCategory.equivAugmentedSimplicialObject.inverse.obj
    (Arrow.mk g).augmentedCechNerve
  have hα : augmentedTupleOpen h U a' t.1 ≤ H.map α.op ⁻¹ᵁ
      augmentedTupleOpen h U a (t.1 ∘ augmentedTupleIndexMap α) := by
    cases a with
    | star => change _ ≤ ⊤; exact le_top
    | of a =>
      cases a' with
      | star => exact PEmpty.elim α
      | of a' =>
        change schemeCechTupleOpen h U (op a') t.1 ≤
          (Arrow.mk h).cechNerve.map (WithInitial.down α).op ⁻¹ᵁ
            schemeCechTupleOpen h U (op a) (t.1 ∘ (WithInitial.down α).toOrderHom)
        exact schemeCechTupleOpen_map_le h U (WithInitial.down α).op t.1
  have hβ : augmentedTupleOpen g V b' t.2 ≤ G.map β.op ⁻¹ᵁ
      augmentedTupleOpen g V b (t.2 ∘ augmentedTupleIndexMap β) := by
    cases b with
    | star => change _ ≤ ⊤; exact le_top
    | of b =>
      cases b' with
      | star => exact PEmpty.elim β
      | of b' =>
        change schemeCechTupleOpen g V (op b') t.2 ≤
          (Arrow.mk g).cechNerve.map (WithInitial.down β).op ⁻¹ᵁ
            schemeCechTupleOpen g V (op b) (t.2 ∘ (WithInitial.down β).toOrderHom)
        exact schemeCechTupleOpen_map_le g V (WithInitial.down β).op t.2
  have hx : pairedCechSchemeMap h g α β ≫
      pullback.fst (augmentedNerveBase h a) (augmentedNerveBase g b) =
      pullback.fst (augmentedNerveBase h a') (augmentedNerveBase g b') ≫ H.map α.op := by
    simp only [pairedCechSchemeMap, pullback.lift_fst, H]
  have hy : pairedCechSchemeMap h g α β ≫
      pullback.snd (augmentedNerveBase h a) (augmentedNerveBase g b) =
      pullback.snd (augmentedNerveBase h a') (augmentedNerveBase g b') ≫ G.map β.op := by
    simp only [pairedCechSchemeMap, pullback.lift_snd, G]
  dsimp only [pairedCechOpen]
  rw [Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage,
    ← Scheme.Hom.comp_preimage, hx, hy, Scheme.Hom.comp_preimage,
    Scheme.Hom.comp_preimage]
  exact inf_le_inf
    ((pullback.fst (augmentedNerveBase h a') (augmentedNerveBase g b')).preimage_mono hα)
    ((pullback.snd (augmentedNerveBase h a') (augmentedNerveBase g b')).preimage_mono hβ)

/-- 元の有限アフィン被覆から、増大点を含む全ての積の次数で同じアフィン被覆を得る。 -/
theorem pairedCechOpen_isAffineOpen_cover {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (h : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    [IsSeparated h] [IsSeparated g]
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (hcU : (⨆ i, U i) = ⊤) (hcV : (⨆ j, V j) = ⊤)
    (a b : AugmentedSimplexCategory) :
    (∀ t, IsAffineOpen (pairedCechOpen h g U V a b t)) ∧
      (⨆ t, pairedCechOpen h g U V a b t) = ⊤ := by
  have ha : ∀ t, IsAffineOpen (augmentedTupleOpen h U a t) := by
    cases a with
    | star =>
      intro t
      change IsAffineOpen (⊤ : (Spec (CommRingCat.of R)).Opens)
      exact isAffineOpen_top _
    | of n => exact schemeCechTupleOpen_isAffine h U hU n.len
  have hb : ∀ t, IsAffineOpen (augmentedTupleOpen g V b t) := by
    cases b with
    | star =>
      intro t
      change IsAffineOpen (⊤ : (Spec (CommRingCat.of R)).Opens)
      exact isAffineOpen_top _
    | of n => exact schemeCechTupleOpen_isAffine g V hV n.len
  have hca : (⨆ t, augmentedTupleOpen h U a t) = ⊤ := by
    cases a with
    | star =>
      change (⨆ _ : Fin 0 → ι, (⊤ : (Spec (CommRingCat.of R)).Opens)) = ⊤
      exact le_antisymm le_top (le_iSup_of_le Fin.elim0 le_rfl)
    | of n => exact schemeCechTupleOpen_iSup h U hcU (op n)
  have hcb : (⨆ t, augmentedTupleOpen g V b t) = ⊤ := by
    cases b with
    | star =>
      change (⨆ _ : Fin 0 → κ, (⊤ : (Spec (CommRingCat.of R)).Opens)) = ⊤
      exact le_antisymm le_top (le_iSup_of_le Fin.elim0 le_rfl)
    | of n => exact schemeCechTupleOpen_iSup g V hcV (op n)
  constructor
  · intro t
    exact pullbackAffineOpen_inf (augmentedNerveBase h a) (augmentedNerveBase g b)
      (ha t.1) (hb t.2)
  · exact schemeCommonOpenCover_iSup
      (fun i ↦ pullback.fst (augmentedNerveBase h a) (augmentedNerveBase g b) ⁻¹ᵁ
        augmentedTupleOpen h U a i)
      (fun j ↦ pullback.snd (augmentedNerveBase h a) (augmentedNerveBase g b) ⁻¹ᵁ
        augmentedTupleOpen g V b j)
      ((pullback.fst (augmentedNerveBase h a) (augmentedNerveBase g b)).iSup_preimage_eq_top hca)
      ((pullback.snd (augmentedNerveBase h a) (augmentedNerveBase g b)).iSup_preimage_eq_top hcb)

end SerrePositivity.AlgebraicGeometry
