module
public import SerrePositivity.DifferentialGraded.Perfect.SmallStages
public import SerrePositivity.DifferentialGraded.Module.ConeFunctor

/-! # 有限cellの段階別代表による同型までの被覆

同型閉包自体を大きい対象型で列挙せず、構成木の帰納法で小さい代表へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- Arrow圏の同型を標準coneの同型へ送る。段階の添字から独立した型でcone関手を適用する。 -/
def moduleConeIsoOfArrowIso {M N M' N' : ModuleCategory A D}
    (f : M ⟶ N) (g : M' ⟶ N') (e : Arrow.mk f ≅ Arrow.mk g) :
    moduleCone A D f ≅ moduleCone A D g :=
  (moduleConeFunctor A D).mapIso (X := Arrow.mk f) (Y := Arrow.mk g) e

/-- 二つの段階の対象を共通の段階へ運ぶ。和とconeの二つの枝に適用する。 -/
lemma moduleFiniteCellStage_pair {S : Set D} (m n : ℕ)
    (i : (moduleFiniteCellStage A D S m).1) (j : (moduleFiniteCellStage A D S n).1) :
    ∃ (k : ℕ) (i' j' : (moduleFiniteCellStage A D S k).1),
      (moduleFiniteCellStage A D S k).2 i' = (moduleFiniteCellStage A D S m).2 i ∧
      (moduleFiniteCellStage A D S k).2 j' = (moduleFiniteCellStage A D S n).2 j := by
  obtain ⟨i', hi⟩ := moduleFiniteCellStage_lift A D S (Nat.le_max_left m n) i
  obtain ⟨j', hj⟩ := moduleFiniteCellStage_lift A D S (Nat.le_max_right m n) j
  exact ⟨max m n, i', j', hi, hj⟩

/-- 有限cellの任意の構成木は、ある小さい段階の対象と厳密な加群同型で結ばれる。 -/
lemma ModuleFiniteCellCode.exists_stage {S : Set D} {M : ModuleCategory A D}
    (c : ModuleFiniteCellCode A D S M) :
    ∃ (n : ℕ) (i : (moduleFiniteCellStage A D S n).1),
      Nonempty (((moduleFiniteCellStage A D S n).2 i).val ≅ M) := by
  induction c with
  | zero => exact ⟨0, .inl PUnit.unit, ⟨Iso.refl _⟩⟩
  | generator x hx =>
    refine ⟨0, .inr (equivShrink S ⟨x, hx⟩), ?_⟩
    simp only [moduleFiniteCellStage, moduleFiniteCellFamilyZero, Equiv.symm_apply_apply]
    exact ⟨Iso.refl _⟩
  | shift s c ih =>
    obtain ⟨n, i, ⟨e⟩⟩ := ih
    exact ⟨n + 1, .inr (.inl (s, i)), ⟨(shiftFunctor _ s).mapIso e⟩⟩
  | @sum M N c d ihc ihd =>
    obtain ⟨m, i, ⟨eM⟩⟩ := ihc
    obtain ⟨n, j, ⟨eN⟩⟩ := ihd
    obtain ⟨k, i', j', hi, hj⟩ := moduleFiniteCellStage_pair A D m n i j
    have eM' : ((moduleFiniteCellStage A D S k).2 i').val ≅ M := by rw [hi]; exact eM
    have eN' : ((moduleFiniteCellStage A D S k).2 j').val ≅ N := by rw [hj]; exact eN
    refine ⟨k + 1, .inr (.inr (.inl (i', j'))), ?_⟩
    exact ⟨moduleBiprodIso A D _ _ ≪≫ biprod.mapIso eM' eN' ≪≫ (moduleBiprodIso A D M N).symm⟩
  | @cone M N c d f ihc ihd =>
    obtain ⟨m, i, ⟨eM⟩⟩ := ihc
    obtain ⟨n, j, ⟨eN⟩⟩ := ihd
    obtain ⟨k, i', j', hi, hj⟩ := moduleFiniteCellStage_pair A D m n i j
    have eM' : ((moduleFiniteCellStage A D S k).2 i').val ≅ M := by rw [hi]; exact eM
    have eN' : ((moduleFiniteCellStage A D S k).2 j').val ≅ N := by rw [hj]; exact eN
    let g := eM'.hom ≫ f ≫ eN'.inv
    refine ⟨k + 1, .inr (.inr (.inr ⟨i', j', g⟩)), ?_⟩
    have e : Arrow.mk g ≅ Arrow.mk f := Arrow.isoMk' g f eM' eN' (by simp [g])
    change Nonempty (moduleCone A D g ≅ moduleCone A D f)
    exact ⟨moduleConeIsoOfArrowIso A D g f e⟩
  | iso c e ih =>
    obtain ⟨n, i, ⟨e'⟩⟩ := ih
    exact ⟨n, i, ⟨e' ≪≫ e⟩⟩

/-- 指定生成集合のfinite cellは小さい段階別代表族で同型まで被覆される。 -/
lemma moduleFiniteCellOver_exists_stage {S : Set D} {M : ModuleCategory A D}
    (hM : moduleFiniteCellOver A D S M) :
    ∃ i : ModuleFiniteCellStageIndex A D S,
      Nonempty (moduleFiniteCellStageObject A D S i ≅ M) := by
  obtain ⟨c⟩ := hM
  obtain ⟨n, i, hi⟩ := c.exists_stage A D
  exact ⟨⟨n, i⟩, hi⟩

end SerrePositivity.DifferentialGraded
