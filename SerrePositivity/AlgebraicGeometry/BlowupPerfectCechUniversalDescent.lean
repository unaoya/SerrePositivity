module

public import SerrePositivity.AlgebraicGeometry.BlowupPerfectCechBaseChangeModel
public import SerrePositivity.AlgebraicGeometry.BlowupPerfectCechCenterDescent
public import SerrePositivity.AlgebraicGeometry.DegreeOneProjectiveCechTupleCenterCriterion

/-!
概要：中心上の普遍Čech降下から、元の全射なブローアップの普遍Čech降下を得る。
方針：各試験基底の同じ射影表示と商環の中心を、既存の中心判定へ代入する。
規約：各有限アフィン被覆を保持し、原典のHⁱではなく同じČech版を使う。
使われ方：Noether閉像帰納の射影的な段（承認済み計画I04）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false

/-- 中心上の完全性を元のブローアップへ戻すČech版。
BST13 Lemma 3.9・BS17 Lemma 4.6(i)に用いる射影Čech版の中心判定を使う。
分離的なスキームの準連接層ではアフィン被覆のČechと一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem perfectCechUniversalDescent_blowup_of_center
    {Y : Scheme.{u}} [IsAffine Y] [_root_.AlgebraicGeometry.IsNoetherian Y]
    (J : Y.IdealSheafData) [Surjective (blowupπ J)] (p : ℕ) (hp : p.Prime)
    (hc : PerfectCechUniversalDescent p hp (pullback.snd (blowupπ J) J.subschemeι)) :
    PerfectCechUniversalDescent p hp (blowupπ J) := by
  intro A _ _ hA t ι _ _ U hU hcU
  let d := blowupPerfectCechBaseChangeData J t
  let g := pullback.snd (blowupπ J) t
  let c := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ 1)))
  haveI : IsClosedImmersion c := by
    dsimp only [c]
    exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  let fI := pullback.snd g c
  let FI : Arrow.mk fI ⟶ Arrow.mk g := Arrow.homMk (pullback.fst g c) c pullback.condition
  haveI : IsAffineHom FI.left := by
    change IsAffineHom (pullback.fst g c)
    infer_instance
  have hq : FI.right = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ 1))) := rfl
  have H : IsPullback FI.left fI g FI.right := IsPullback.of_hasPullback g c
  have hd := blowupBaseChange_center_universalDescent J t d p hp hc
  let B := A ⧸ d.ideal ^ 1
  let hB : (p : B) = 0 := frobeniusQuotientPrimeCast p hA (d.ideal ^ 1)
  let V (i : ι) := FI.left ⁻¹ᵁ U i
  have hV (i) : IsAffineOpen (V i) := (hU i).preimage FI.left
  have hcV : (⨆ i, V i) = ⊤ := FI.left.iSup_preimage_eq_top hcU
  let F0 : Arrow.mk (pullback.snd fI (𝟙 (Spec (CommRingCat.of B)))) ⟶ Arrow.mk fI :=
    Arrow.homMk (pullback.fst fI (𝟙 _)) (𝟙 _) pullback.condition
  haveI : IsIso F0.left := by
    change IsIso (pullback.fst fI (𝟙 (Spec (CommRingCat.of B))))
    infer_instance
  haveI : IsIso F0.right := by
    change IsIso (𝟙 (Spec (CommRingCat.of B)))
    infer_instance
  have H0 : IsPullback F0.left (pullback.snd fI (𝟙 (Spec (CommRingCat.of B)))) fI F0.right :=
    IsPullback.of_hasPullback fI (𝟙 _)
  have hq0 : F0.right = Spec.map (CommRingCat.ofHom (RingHom.id B)) :=
    (Spec.map_id _).symm
  have hCenter := (nilBaseChange_tupleTotal_acyclic_iff
    (pullback.snd fI (𝟙 (Spec (CommRingCat.of B)))) fI F0 H0 (RingHom.id B) hq0
      p hp hB hB V hV).mpr
        (hd B hB (𝟙 _) ι (fun i ↦ F0.left ⁻¹ᵁ V i)
          (fun i ↦ (hV i).preimage F0.left) (F0.left.iSup_preimage_eq_top hcV))
  haveI : IsIso (g ∣_ affineCenterComplement d.ideal) := d.outside
  exact DegreeOneProjectiveModel.perfectCechTupleTotal_acyclic_of_center
    g U p hp hA d.ideal fI FI hq d.model H hU hcU hCenter

end SerrePositivity.AlgebraicGeometry
