module

public import SerrePositivity.AlgebraicGeometry.PairedPerfectCechSectionColumns
public import SerrePositivity.AlgebraicGeometry.PairedPerfectCechBaseChangeRows
public import SerrePositivity.AlgebraicGeometry.PairedPerfectCechZeroRow
public import SerrePositivity.AlgebraicGeometry.ComplexValuedDoubleCechSymmetry
public import SerrePositivity.AlgebraicGeometry.PerfectCechUniversalBaseChange
public import SerrePositivity.AlgebraicGeometry.NilBaseChangePerfectCech

/-!
概要：アフィンな合成の降下性から元の射の普遍Čech降下性を得る。
方針：元の合成のnerveの第一座標に切断を作り、同じ二変数図式の零次軸を比較する。
規約：元の各試験基底と有限アフィン被覆を保持する。
使われ方：相対fppf・Rydhの細分の消去（承認済み計画D06）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicTopology
universe u
set_option backward.isDefEq.respectTransparency false

/-- 同じアフィン細分の普遍降下性を、元の射へ反映するČech版。 -/
theorem perfectCechUniversalDescent_of_affine_refinement
    (p : ℕ) (hp : p.Prime) {X Y A : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [QuasiCompact f] [LocallyOfFinitePresentation f]
    (a : A ⟶ X) [IsAffineHom (a ≫ f)] [LocallyOfFinitePresentation (a ≫ f)]
    (ha : PerfectCechUniversalDescent p hp (a ≫ f)) :
    PerfectCechUniversalDescent p hp f := by
  intro R _ _ hR t ι _ _ U hU hcU
  let g := pullback.snd f t
  let h := pullback.snd (a ≫ f) t
  let k : pullback (a ≫ f) t ⟶ pullback f t :=
    pullback.lift (pullback.fst (a ≫ f) t ≫ a) h (by
      rw [Category.assoc]
      exact pullback.condition)
  have hk : k ≫ g = h := pullback.lift_snd _ _ _
  have hh := perfectCechUniversalDescent_baseChange p hp (a ≫ f) t ha
  let W : Unit → (pullback (a ≫ f) t).Opens := fun _ ↦ ⊤
  have hW (i : Unit) : IsAffineOpen (W i) := isAffineOpen_top _
  have hcW : (⨆ i, W i) = ⊤ := by simp [W]
  let F : Arrow.mk (pullback.snd h (𝟙 (Spec (CommRingCat.of R)))) ⟶ Arrow.mk h :=
    Arrow.homMk (pullback.fst h (𝟙 _)) (𝟙 _) pullback.condition
  haveI : IsIso F.left := by change IsIso (pullback.fst h (𝟙 _)); infer_instance
  haveI : IsIso F.right := by change IsIso (𝟙 (Spec (CommRingCat.of R))); infer_instance
  have H : IsPullback F.left (pullback.snd h (𝟙 (Spec (CommRingCat.of R)))) h F.right :=
    IsPullback.of_hasPullback h (𝟙 _)
  have hbase : F.right = Spec.map (CommRingCat.ofHom (RingHom.id R)) := (Spec.map_id _).symm
  have hPC := (nilBaseChange_tupleTotal_acyclic_iff
    (pullback.snd h (𝟙 (Spec (CommRingCat.of R)))) h F H (RingHom.id R) hbase
      p hp hR hR W hW).mpr
        (hh R hR (𝟙 _) Unit (fun i ↦ F.left ⁻¹ᵁ W i)
          (fun i ↦ (hW i).preimage F.left) (F.left.iSup_preimage_eq_top hcW))
  have hσ (i : ℕ) (hi : 0 < i) :
      ∃ s, s ≫ pullback.snd g (augmentedNerveBase h (SerrePositivity.Cech.simplex i)) = 𝟙 _ := by
    cases i with
    | zero => omega
    | succ n =>
      let v := WidePullback.π (fun _ : Fin (n+1) ↦ h) 0
      refine ⟨pullback.lift (v ≫ k) (𝟙 _) ?_, pullback.lift_snd _ _ _⟩
      change (v ≫ k) ≫ g = (𝟙 _) ≫ WidePullback.base (fun _ : Fin (n+1) ↦ h)
      rw [Category.assoc, hk, Category.id_comp]
      exact WidePullback.π_arrow _ _
  have hcol := pairedCech_col_acyclic_of_sections h g U hU hcU p hp hR hσ
  have hrow := pairedCech_row_acyclic_of_baseChangeDescent h g U hU hcU p hp hR
    (fun j _ ↦ perfectCechUniversalDescent_baseChange p hp h
      (augmentedNerveBase g (SerrePositivity.Cech.simplex j)) hh)
  let D := pairedPerfectCech h g W U p hp hR
  have hrow0 := (pairedPerfectCech_zero_row_acyclic_iff h g W U p hp hR).mpr hPC
  have hcol0 := (complexValuedDoubleCech_axes_acyclic_iff D hcol hrow).mpr hrow0
  exact (pairedPerfectCech_zero_col_acyclic_iff h g W U p hp hR).mp hcol0

end SerrePositivity.AlgebraicGeometry
