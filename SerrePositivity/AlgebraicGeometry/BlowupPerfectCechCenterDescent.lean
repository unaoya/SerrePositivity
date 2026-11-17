module

public import SerrePositivity.AlgebraicGeometry.BlowupPerfectCechBaseChangeData
public import SerrePositivity.AlgebraicGeometry.PerfectCechUniversalBaseChange
public import SerrePositivity.AlgebraicGeometry.NilBaseChangePerfectCech
public import SerrePositivity.AlgebraicGeometry.SchemeBlowupProper
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
概要：元の中心上の降下性を、同じアフィン試験基底の商環の中心へ移す。
方針：元の中心への射を因子化し、同じ反復pullbackの標準同型と係数の同型を使う。
規約：中心の厚みと元の試験写像を保持する。
使われ方：ブローアップの普遍Čech降下性（承認済み計画I03）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false

/-- 元の中心の普遍降下性は、同じ試験基底の商環表示の中心へ移る。 -/
theorem blowupBaseChange_center_universalDescent
    {Y : Scheme.{u}} (J : Y.IdealSheafData) {A : Type u} [CommRing A]
    (t : Spec (CommRingCat.of A) ⟶ Y) (d : BlowupPerfectCechBaseChangeData J t)
    (p : ℕ) (hp : p.Prime)
    (hc : PerfectCechUniversalDescent p hp (pullback.snd (blowupπ J) J.subschemeι)) :
    PerfectCechUniversalDescent p hp
      (pullback.snd (pullback.snd (blowupπ J) t)
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ 1))))) := by
  let c := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ 1)))
  let l := d.centerIso.inv ≫ (J.comap t).subschemeMap J t (J.le_map_comap t)
  have he : d.centerIso.inv ≫ (J.comap t).subschemeι = c :=
    (d.centerIso.inv_comp_eq).mpr d.center_over.symm
  have hl : l ≫ J.subschemeι = c ≫ t := by
    dsimp only [l]
    rw [Category.assoc, Scheme.IdealSheafData.subschemeMap_subschemeι,
      ← Category.assoc, he]
  intro R _ _ hR u ι _ _ U hU hcU
  let g := pullback.snd (blowupπ J) J.subschemeι
  let q := pullback.snd (pullback.snd (blowupπ J) t) c
  have hb : (u ≫ c) ≫ t = (u ≫ l) ≫ J.subschemeι := by
    rw [Category.assoc, Category.assoc, hl]
  let E : pullback q u ≅ pullback g (u ≫ l) :=
    pullbackLeftPullbackSndIso (pullback.snd (blowupπ J) t) c u ≪≫
      pullbackLeftPullbackSndIso (blowupπ J) t (u ≫ c) ≪≫
        pullback.congrHom (f₁ := blowupπ J) rfl hb ≪≫
          (pullbackLeftPullbackSndIso (blowupπ J) J.subschemeι (u ≫ l)).symm
  have hcong {a b : Spec (CommRingCat.of R) ⟶ Y} (hab : a = b) :
      (pullback.congrHom (f₁ := blowupπ J) rfl hab).hom ≫ pullback.snd (blowupπ J) b =
        pullback.snd (blowupπ J) a := by
    subst b
    simp
  have hE : E.hom ≫ pullback.snd g (u ≫ l) = pullback.snd q u := by
    dsimp only [E, g, q]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
      pullbackLeftPullbackSndIso_inv_snd_snd, hcong, Category.comp_id,
      pullbackLeftPullbackSndIso_hom_snd]
  let V (i : ι) := E.inv ⁻¹ᵁ U i
  have hV (i) : IsAffineOpen (V i) := (hU i).preimage E.inv
  have hcV : (⨆ i, V i) = ⊤ := E.inv.iSup_preimage_eq_top hcU
  have hPC := hc R hR (u ≫ l) ι V hV hcV
  let F : Arrow.mk (pullback.snd q u) ⟶ Arrow.mk (pullback.snd g (u ≫ l)) :=
    Arrow.homMk E.hom (𝟙 _) (hE.trans (Category.comp_id _).symm)
  haveI : IsIso F.left := by change IsIso E.hom; infer_instance
  haveI : IsIso F.right := by change IsIso (𝟙 (Spec (CommRingCat.of R))); infer_instance
  have H : IsPullback F.left (pullback.snd q u) (pullback.snd g (u ≫ l)) F.right :=
    IsPullback.of_horiz_isIso ⟨F.w⟩
  have hbase : F.right = Spec.map (CommRingCat.ofHom (RingHom.id R)) :=
    (Spec.map_id _).symm
  have hQ := (nilBaseChange_tupleTotal_acyclic_iff
    (pullback.snd q u) (pullback.snd g (u ≫ l)) F H (RingHom.id R) hbase
      p hp hR hR V hV).mp hPC
  have hcover : (fun i ↦ F.left ⁻¹ᵁ V i) = U := by
    funext i
    change E.hom ⁻¹ᵁ (E.inv ⁻¹ᵁ U i) = U i
    rw [← Scheme.Hom.comp_preimage, E.hom_inv_id, Scheme.Hom.id_preimage]
  exact hcover ▸ hQ

end SerrePositivity.AlgebraicGeometry
