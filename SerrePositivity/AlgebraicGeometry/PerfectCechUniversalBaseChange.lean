module

public import SerrePositivity.AlgebraicGeometry.PerfectCechUniversalDescent
public import SerrePositivity.AlgebraicGeometry.SchemeStructurePerfectCechIso
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleAugmentedPullback
public import SerrePositivity.AlgebraicGeometry.CechIntegerLiftTotalFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
概要：実際の完全構造層の普遍Čech降下性を任意の底変換へ渡す。
方針：反復pullbackの同型とその逆像被覆を、同じ増大係数の射に写す。
規約：Noetherアフィン試験基底と元の係数を保持する。分離性を追加しない。
使われ方：相対fppfと閉像の帰納（承認済み計画D02）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
local notation "up" => ComplexShape.up ℕ
set_option backward.isDefEq.respectTransparency false

/-- 同じ試験基底の反復pullbackと逆像被覆で、普遍降下性を底変換へ渡す。 -/
theorem perfectCechUniversalDescent_baseChange
    (p : ℕ) (hp : p.Prime) {X Y T : Scheme.{u}} (f : X ⟶ Y) (t : T ⟶ Y)
    (hf : PerfectCechUniversalDescent p hp f) :
    PerfectCechUniversalDescent p hp (pullback.snd f t) := by
  intro R _ _ hR a ι _ _ U hU hcU
  let e := pullbackLeftPullbackSndIso f t a
  let g := pullback.snd f (a ≫ t)
  let q := pullback.snd (pullback.snd f t) a
  have he : e.hom ≫ g = q := pullbackLeftPullbackSndIso_hom_snd f t a
  let V (i : ι) := e.inv ⁻¹ᵁ U i
  have hV (i : ι) : IsAffineOpen (V i) := (hU i).preimage e.inv
  have hcV : (⨆ i, V i) = ⊤ := e.inv.iSup_preimage_eq_top hcU
  have hPC := hf R hR (a ≫ t) ι V hV hcV
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

end SerrePositivity.AlgebraicGeometry
