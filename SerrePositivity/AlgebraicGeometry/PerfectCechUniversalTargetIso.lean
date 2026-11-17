module

public import SerrePositivity.AlgebraicGeometry.PerfectCechUniversalDescent
public import SerrePositivity.AlgebraicGeometry.SchemeStructurePerfectCechIso
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleAugmentedPullback
public import SerrePositivity.AlgebraicGeometry.CechIntegerLiftTotalFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
概要：実際の完全構造層の普遍Čech降下性を終域の同型に沿って比較する。
方針：反復pullbackの同型とその逆像被覆を、同じ増大係数の射に写す。
規約：Noetherアフィン試験基底と元の係数を保持する。分離性を追加しない。
使われ方：相対fppfと閉像の帰納（承認済み計画D08）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
local notation "up" => ComplexShape.up ℕ
set_option backward.isDefEq.respectTransparency false

/-- 終域の同型に沿って、同じ普遍Čech降下性を保ち反映する。 -/
theorem perfectCechUniversalDescent_targetIso
    (p : ℕ) (hp : p.Prime) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (e : Y ≅ Z) :
    PerfectCechUniversalDescent p hp (f ≫ e.hom) ↔ PerfectCechUniversalDescent p hp f := by
  have H : ∀ {A B C : Scheme.{u}} (f : A ⟶ B) (j : B ≅ C),
      PerfectCechUniversalDescent p hp f → PerfectCechUniversalDescent p hp (f ≫ j.hom) := by
    intro A B C f j hf
    intro R _ _ hR a ι _ _ U hU hcU
    let e : pullback (f ≫ j.hom) a ≅ pullback f (a ≫ j.inv) :=
      { hom := pullback.map _ _ _ _ (𝟙 _) (𝟙 _) j.inv
          (by simp only [Category.assoc, j.hom_inv_id, Category.comp_id, Category.id_comp])
          (by simp only [Category.id_comp])
        inv := pullback.map _ _ _ _ (𝟙 _) (𝟙 _) j.hom
          (by simp only [Category.id_comp])
          (by simp only [Category.assoc, j.inv_hom_id, Category.comp_id, Category.id_comp])
        hom_inv_id := by
          apply pullback.hom_ext <;> simp [pullback.map, Category.assoc]
        inv_hom_id := by
          apply pullback.hom_ext <;> simp [pullback.map, Category.assoc] }
    let g := pullback.snd f (a ≫ j.inv)
    let q := pullback.snd (f ≫ j.hom) a
    have he : e.hom ≫ g = q := by simp [e, g, q, pullback.map]
    letI : IsIso e.inv := e.isIso_inv
    let V (i : ι) := e.inv ⁻¹ᵁ U i
    have hV (i : ι) : IsAffineOpen (V i) := (hU i).preimage e.inv
    have hcV : (⨆ i, V i) = ⊤ := e.inv.iSup_preimage_eq_top hcU
    have hPC := hf R hR (a ≫ j.inv) ι V hV hcV
    let E : Arrow.mk q ≅ Arrow.mk g := Arrow.isoMk e (Iso.refl _) (by
      change e.hom ≫ g = q ≫ 𝟙 _
      exact he.trans (Category.comp_id q).symm)
    let F := E.hom
    have hq : F.right = Spec.map (CommRingCat.ofHom (RingHom.id R)) := by
      change 𝟙 _ = Spec.map (𝟙 _)
      exact (Spec.map_id _).symm
    let M := schemePerfectCechTupleAugmentedPullback q g F (RingHom.id R) hq V p hp hR hR
    haveI : IsIso M.left := by
      dsimp only [M, schemePerfectCechTupleAugmentedPullback]
      rw [frobeniusDirectLimitMap_id]
      change IsIso ((HomologicalComplex.single (ModuleCat.{u} ℤ) up 0).map
        (𝟙 (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR))))
      infer_instance
    haveI : ∀ n : SimplexCategory, IsIso (M.right.app n) := fun n ↦ by
      let v := (Arrow.mapCechNerve F).app (op n)
      haveI : IsIso v := by
        change IsIso ((SimplicialObject.cechNerve.map E.hom).app (op n))
        infer_instance
      let hg := schemeCechNervePresheaf_primeCast g p hR (op n)
      let hq := schemeCechNervePresheaf_primeCast q p hR (op n)
      let P := frobeniusRingDiagram ((Arrow.mk q).cechNerve.obj (op n)).presheaf p hp hq
      let W := schemeCechTupleOpen g V (op n)
      let A := fun z ↦ v ⁻¹ᵁ W z
      let B := schemeCechTupleOpen q (fun i ↦ F.left ⁻¹ᵁ V i) (op n)
      have hAB : A = B := funext fun z ↦
        (schemeCechTupleOpen_mapCechNerve_preimage F V (op n) z).symm
      have hRef : ∀ hb : ∀ z, B z ≤ A z,
          IsIso (openCoverCechRefinementMap P A B id hb) :=
        Eq.rec (motive := fun B _ ↦ ∀ hb : ∀ z, B z ≤ A z,
          IsIso (openCoverCechRefinementMap P A B id hb))
          (by intro hb; rw [openCoverCechRefinementMap_id]; infer_instance) hAB
      haveI : IsIso (schemeStructurePerfectCechPullbackMap v p hp hg hq W) :=
        schemeStructurePerfectCechPullbackMap_isIso v p hp hg hq W
      haveI : IsIso (openCoverCechRefinementMap P A B id
          (fun z ↦ le_of_eq (schemeCechTupleOpen_mapCechNerve_preimage F V (op n) z))) := hRef _
      change IsIso (schemeStructurePerfectCechPullbackMap v p hp hg hq W ≫
        openCoverCechRefinementMap P A B id
          (fun z ↦ le_of_eq (schemeCechTupleOpen_mapCechNerve_preimage F V (op n) z)))
      infer_instance
    haveI : IsIso M.right := NatIso.isIso_of_isIso_app _
    let em := Comma.isoMk (asIso M.left) (asIso M.right) M.w
    have hem : em.hom = M := by apply Comma.hom_ext <;> rfl
    haveI : IsIso M := by rw [← hem]; infer_instance
    let ec := cechIntegerLiftTotalFunctor.mapIso
      (SerrePositivity.Cech.augmentedCochain.mapIso (asIso M))
    have hUV : (fun i ↦ F.left ⁻¹ᵁ V i) = U := by
      funext i
      change e.hom ⁻¹ᵁ (e.inv ⁻¹ᵁ U i) = U i
      rw [← Scheme.Hom.comp_preimage, e.hom_inv_id, Scheme.Hom.id_preimage]
    have hc : (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
        (schemePerfectCechTupleDouble q (fun i ↦ F.left ⁻¹ᵁ V i) p hp hR) up).Acyclic :=
      fun n ↦ (hPC n).of_iso ec
    rw [hUV] at hc
    exact hc
  constructor
  · intro h
    simpa only [Category.assoc, Iso.symm_hom, e.hom_inv_id, Category.comp_id] using
      H (f ≫ e.hom) e.symm h
  · exact H f e

end SerrePositivity.AlgebraicGeometry
