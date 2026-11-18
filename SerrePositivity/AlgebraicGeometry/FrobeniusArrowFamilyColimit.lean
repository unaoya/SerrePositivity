module

public import SerrePositivity.AlgebraicGeometry.FrobeniusArrowFamilyCocones
public import SerrePositivity.HomologicalAlgebra.Cech.Filtered

/-!
概要：模型の余極限と Frobenius 順極限を、元の矢印と標準脚を保って交換する。
方針：既存の Fubini 同型と各段の余錐の普遍性を合成し、B1 の filtered 完全性を使う。
規約：終点の係数写像は元の矢印の実際の Frobenius 写像である。
使われ方：有限型の被覆模型から元の環へ Čech 完全性を戻す（計画 E11〜E14）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false

/-- 実際の Frobenius 順極限に送った元の余錐は、同じ矢印の族の余極限。 -/
def frobeniusArrowFamilyTargetCoconeIsColimit {J : Type u} [SmallCategory J]
    (D : J ⥤ Arrow CommRingCat.{u}) (p : ℕ) (hp : p.Prime)
    (hL : ∀ j, (p : (D.obj j).left) = 0) (hR : ∀ j, (p : (D.obj j).right) = 0)
    (c : Cocone D) (hTL : (p : c.pt.left) = 0) (hTR : (p : c.pt.right) = 0)
    (hc : IsColimit c) :
    IsColimit (frobeniusArrowFamilyTargetCocone D p hp hL hR c hTL hTR) := by
  let F := frobeniusArrowFamilyDiagram D p hp hL hR
  let A := frobeniusArrowFamilyLimit D p hp hL hR
  let es := frobeniusArrowFamilyStandardIso D p hp hL hR
  let ec := frobeniusArrowFamilyStageColimitIso D p hp hL hR c hTL hTR hc
  let ep := frobeniusArrowSmallColimitIso c.pt p hp hTL hTR
  let ef := frobeniusArrowFamilyFubiniIso D p hp hL hR
  let e := HasColimit.isoOfNatIso es ≪≫
    (ef.symm ≪≫ (HasColimit.isoOfNatIso ec ≪≫ ep.symm))
  refine IsColimit.ofIsoColimit (colimit.isColimit A) (Cocone.ext e ?_)
  intro j
  apply (frobeniusArrowSmallIsColimit (D.obj j) p hp (hL j) (hR j)).hom_ext
  intro n
  let t0 := ef.inv ≫ (HasColimit.isoOfNatIso ec).hom ≫ ep.inv
  let t1 := (HasColimit.isoOfNatIso ec).hom ≫ ep.inv
  let iD := (frobeniusArrowSmallCocone (D.obj j) p hp (hL j) (hR j)).ι.app n
  let iC := (frobeniusArrowSmallCocone c.pt p hp hTL hTR).ι.app n
  let iS := colimit.ι (frobeniusArrowSmallDiagram c.pt p hp hTL hTR) n
  change iD ≫ colimit.ι A j ≫ (HasColimit.isoOfNatIso es).hom ≫ t0 =
    iD ≫ frobeniusDirectLimitArrowMap (c.ι.app j) p hp (hL j) (hR j) hTL hTR
  have hfirst : iD ≫ es.hom.app j = colimit.ι (F.obj j) n :=
    frobeniusArrowSmallColimitIso_ι (f := D.obj j) p hp (hL j) (hR j) n
  have hstage : colimit.ι (F.flip.obj n) j ≫ ec.hom.app n = c.ι.app j :=
    frobeniusArrowFamilyStageColimitIso_ι D p hp hL hR c hTL hTR hc j n
  have hlast : iS ≫ ep.inv = iC :=
    (frobeniusArrowSmallIsColimit c.pt p hp hTL hTR).comp_coconePointUniqueUpToIso_inv
      (colimit.isColimit _) n
  calc
    _ = iD ≫ es.hom.app j ≫ colimit.ι (F ⋙ colim) j ≫ t0 :=
      congrArg (fun r ↦ iD ≫ r) (HasColimit.ι_isoOfNatIso_hom_assoc es j t0)
    _ = colimit.ι (F.obj j) n ≫ colimit.ι (F ⋙ colim) j ≫ t0 :=
      (Category.assoc iD (es.hom.app j) (colimit.ι (F ⋙ colim) j ≫ t0)).symm.trans
        (congrArg (fun r ↦ r ≫ colimit.ι (F ⋙ colim) j ≫ t0) hfirst)
    _ = colimit.ι (F.flip.obj n) j ≫ colimit.ι (F.flip ⋙ colim) n ≫ t1 :=
      colimitFlipCompColimIsoColimitCompColim_ι_ι_inv_assoc F n j t1
    _ = colimit.ι (F.flip.obj n) j ≫ ec.hom.app n ≫ iS ≫ ep.inv :=
      congrArg (fun r ↦ colimit.ι (F.flip.obj n) j ≫ r)
        (HasColimit.ι_isoOfNatIso_hom_assoc ec n ep.inv)
    _ = c.ι.app j ≫ iS ≫ ep.inv :=
      (Category.assoc (colimit.ι (F.flip.obj n) j) (ec.hom.app n) (iS ≫ ep.inv)).symm.trans
        (congrArg (fun r ↦ r ≫ iS ≫ ep.inv) hstage)
    _ = c.ι.app j ≫ iC := congrArg (fun r ↦ c.ι.app j ≫ r) hlast
    _ = _ := (frobeniusArrowCocone_map (c.ι.app j) p hp
      (hL j) (hR j) hTL hTR n).symm

/-- 元の矢印の実際の Frobenius 順極限と、模型の順極限の標準同型。 -/
def frobeniusArrowFamilyColimitIso {J : Type u} [SmallCategory J]
    (D : J ⥤ Arrow CommRingCat.{u}) (p : ℕ) (hp : p.Prime)
    (hL : ∀ j, (p : (D.obj j).left) = 0) (hR : ∀ j, (p : (D.obj j).right) = 0)
    (c : Cocone D) (hTL : (p : c.pt.left) = 0) (hTR : (p : c.pt.right) = 0)
    (hc : IsColimit c) :
    colimit (frobeniusArrowFamilyLimit D p hp hL hR) ≅
      Arrow.mk (CommRingCat.ofHom (frobeniusDirectLimitMap p hp hTL hTR c.pt.hom.hom)) :=
  (colimit.isColimit _).coconePointUniqueUpToIso
    (frobeniusArrowFamilyTargetCoconeIsColimit D p hp hL hR c hTL hTR hc)

/-- 同じ標準同型は、各模型の元の脚の実際の Frobenius 写像を保つ。 -/
theorem frobeniusArrowFamilyColimitIso_ι {J : Type u} [SmallCategory J]
    (D : J ⥤ Arrow CommRingCat.{u}) (p : ℕ) (hp : p.Prime)
    (hL : ∀ j, (p : (D.obj j).left) = 0) (hR : ∀ j, (p : (D.obj j).right) = 0)
    (c : Cocone D) (hTL : (p : c.pt.left) = 0) (hTR : (p : c.pt.right) = 0)
    (hc : IsColimit c) (j : J) :
    colimit.ι (frobeniusArrowFamilyLimit D p hp hL hR) j ≫
      (frobeniusArrowFamilyColimitIso D p hp hL hR c hTL hTR hc).hom =
        frobeniusDirectLimitArrowMap (c.ι.app j) p hp (hL j) (hR j) hTL hTR :=
  (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom
    (frobeniusArrowFamilyTargetCoconeIsColimit D p hp hL hR c hTL hTR hc) j

/-- 同じ filtered 被覆模型の実際の完全化の Čech 完全性は、元の係数の完全化へ戻る。 -/
theorem frobeniusCechExact_of_filtered_arrow_models {J : Type u} [SmallCategory J]
    (D : J ⥤ Arrow CommRingCat.{u}) (p : ℕ) (hp : p.Prime)
    (hL : ∀ j, (p : (D.obj j).left) = 0) (hR : ∀ j, (p : (D.obj j).right) = 0)
    (c : Cocone D) (hTL : (p : c.pt.left) = 0) (hTR : (p : c.pt.right) = 0)
    [IsFiltered J] (hc : IsColimit c)
    (hd : ∀ j, SerrePositivity.Cech.IsCechExact
      (Arrow.mk (CommRingCat.ofHom
        (frobeniusDirectLimitMap p hp (hL j) (hR j) (D.obj j).hom.hom)))) :
    SerrePositivity.Cech.IsCechExact
      (Arrow.mk (CommRingCat.ofHom (frobeniusDirectLimitMap p hp hTL hTR c.pt.hom.hom))) := by
  have h := SerrePositivity.Cech.isCechExact_colimit (frobeniusArrowFamilyLimit D p hp hL hR) hd
  exact (SerrePositivity.Cech.ringCechExact_iff_of_iso
    (CosimplicialObject.augmentedCechConerve.mapIso
      (frobeniusArrowFamilyColimitIso D p hp hL hR c hTL hTR hc))).mp h

end SerrePositivity.AlgebraicGeometry
