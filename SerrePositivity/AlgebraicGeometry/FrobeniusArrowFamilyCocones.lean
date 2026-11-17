module

public import SerrePositivity.AlgebraicGeometry.FrobeniusArrowFamily

/-!
概要：元の矢印の族の余錐を、実際の Frobenius 順極限と有限段の族へ移す。
方針：既存の写像の合成則を使い、各固定段の元の余錐から標準比較を作る。
規約：元の矢印と同じ標準脚を保持し、filtered 性はここでは仮定しない。
使われ方：二変数の余極限の交換と模型の完全性の移送（計画 E04〜E09）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false

/-- 元の余錐の標準脚に実際の Frobenius 順極限を適用した余錐。 -/
def frobeniusArrowFamilyTargetCocone {J : Type u} [SmallCategory J]
    (D : J ⥤ Arrow CommRingCat.{u}) (p : ℕ) (hp : p.Prime)
    (hL : ∀ j, (p : (D.obj j).left) = 0) (hR : ∀ j, (p : (D.obj j).right) = 0)
    (c : Cocone D) (hTL : (p : c.pt.left) = 0) (hTR : (p : c.pt.right) = 0) :
    Cocone (frobeniusArrowFamilyLimit D p hp hL hR) where
  pt := Arrow.mk (CommRingCat.ofHom (frobeniusDirectLimitMap p hp hTL hTR c.pt.hom.hom))
  ι :=
    { app := fun j ↦ frobeniusDirectLimitArrowMap (c.ι.app j) p hp (hL j) (hR j) hTL hTR
      naturality := by
        intro j k f
        change frobeniusDirectLimitArrowMap (D.map f) p hp (hL j) (hR j) (hL k) (hR k) ≫
            frobeniusDirectLimitArrowMap (c.ι.app k) p hp (hL k) (hR k) hTL hTR =
          frobeniusDirectLimitArrowMap (c.ι.app j) p hp (hL j) (hR j) hTL hTR ≫ 𝟙 _
        rw [Category.comp_id, ← frobeniusDirectLimitArrowMap_comp, c.w f] }

/-- 同じ余錐の脚は、元の脚の実際の Frobenius 写像そのもの。 -/
theorem frobeniusArrowFamilyTargetCocone_ι {J : Type u} [SmallCategory J]
    (D : J ⥤ Arrow CommRingCat.{u}) (p : ℕ) (hp : p.Prime)
    (hL : ∀ j, (p : (D.obj j).left) = 0) (hR : ∀ j, (p : (D.obj j).right) = 0)
    (c : Cocone D) (hTL : (p : c.pt.left) = 0) (hTR : (p : c.pt.right) = 0) (j : J) :
    (frobeniusArrowFamilyTargetCocone D p hp hL hR c hTL hTR).ι.app j =
      frobeniusDirectLimitArrowMap (c.ι.app j) p hp (hL j) (hR j) hTL hTR := rfl

/-- Frobenius の固定した有限段の族の余錐は、元の余錐の同じ脚を持つ。 -/
def frobeniusArrowFamilyStageCocone {J : Type u} [SmallCategory J]
    (D : J ⥤ Arrow CommRingCat.{u}) (p : ℕ) (hp : p.Prime)
    (hL : ∀ j, (p : (D.obj j).left) = 0) (hR : ∀ j, (p : (D.obj j).right) = 0)
    (c : Cocone D) (n : AsSmall.{u} ℕ) :
    Cocone ((frobeniusArrowFamilyDiagram D p hp hL hR).flip.obj n) where
  pt := c.pt
  ι :=
    { app := fun j ↦ c.ι.app j
      naturality := by intro j k f; exact c.ι.naturality f }

/-- 固定した有限段の族では、元の余錐の余極限の普遍性を使う。 -/
def frobeniusArrowFamilyStageCoconeIsColimit {J : Type u} [SmallCategory J]
    (D : J ⥤ Arrow CommRingCat.{u}) (p : ℕ) (hp : p.Prime)
    (hL : ∀ j, (p : (D.obj j).left) = 0) (hR : ∀ j, (p : (D.obj j).right) = 0)
    (c : Cocone D) (hc : IsColimit c) (n : AsSmall.{u} ℕ) :
    IsColimit (frobeniusArrowFamilyStageCocone D p hp hL hR c n) := by
  let forgetStage : Cocone ((frobeniusArrowFamilyDiagram D p hp hL hR).flip.obj n) →
      Cocone D := fun s ↦
    { pt := s.pt
      ι :=
        { app := fun j ↦ s.ι.app j
          naturality := by intro j k f; exact s.ι.naturality f } }
  exact
    { desc := fun s ↦ hc.desc (forgetStage s)
      fac := fun s j ↦ hc.fac (forgetStage s) j
      uniq := fun s m hm ↦ hc.uniq (forgetStage s) m hm }

/-- 固定段の族の圏論的余極限と、元の余錐の同じ有限段との自然同型。 -/
def frobeniusArrowFamilyStageColimitIso {J : Type u} [SmallCategory J]
    (D : J ⥤ Arrow CommRingCat.{u}) (p : ℕ) (hp : p.Prime)
    (hL : ∀ j, (p : (D.obj j).left) = 0) (hR : ∀ j, (p : (D.obj j).right) = 0)
    (c : Cocone D) (hTL : (p : c.pt.left) = 0) (hTR : (p : c.pt.right) = 0)
    (hc : IsColimit c) :
    (frobeniusArrowFamilyDiagram D p hp hL hR).flip ⋙ colim ≅
      frobeniusArrowSmallDiagram c.pt p hp hTL hTR :=
  NatIso.ofComponents (fun _ ↦ (colimit.isColimit D).coconePointUniqueUpToIso hc) (by
    intro n m a
    let δ : D ⟶ D :=
      { app := fun j ↦ (frobeniusArrowSmallDiagram (D.obj j) p hp (hL j) (hR j)).map a
        naturality := by
          intro j k f
          exact (frobeniusArrowSmallDiagramMap (D.map f) p hp
            (hL j) (hR j) (hL k) (hR k)).naturality a |>.symm }
    change colim.map δ ≫ ((colimit.isColimit D).coconePointUniqueUpToIso hc).hom =
      ((colimit.isColimit D).coconePointUniqueUpToIso hc).hom ≫
        (frobeniusArrowSmallDiagram c.pt p hp hTL hTR).map a
    apply (colimit.isColimit D).hom_ext
    intro j
    let e := (colimit.isColimit D).coconePointUniqueUpToIso hc
    have hι : colimit.ι D j ≫ e.hom = c.ι.app j :=
      (colimit.isColimit D).comp_coconePointUniqueUpToIso_hom hc j
    calc
      _ = δ.app j ≫ colimit.ι D j ≫ e.hom := colimit.ι_map_assoc δ j e.hom
      _ = δ.app j ≫ c.ι.app j := congrArg (fun r ↦ δ.app j ≫ r) hι
      _ = c.ι.app j ≫ (frobeniusArrowSmallDiagram c.pt p hp hTL hTR).map a :=
        (frobeniusArrowSmallDiagramMap (c.ι.app j) p hp
          (hL j) (hR j) hTL hTR).naturality a
      _ = (colimit.ι D j ≫ e.hom) ≫
          (frobeniusArrowSmallDiagram c.pt p hp hTL hTR).map a :=
        (congrArg (fun r ↦ r ≫ (frobeniusArrowSmallDiagram c.pt p hp hTL hTR).map a) hι).symm
      _ = _ := Category.assoc _ _ _)

/-- 同じ有限段の標準比較は、元の余錐の脚を保つ。 -/
theorem frobeniusArrowFamilyStageColimitIso_ι {J : Type u} [SmallCategory J]
    (D : J ⥤ Arrow CommRingCat.{u}) (p : ℕ) (hp : p.Prime)
    (hL : ∀ j, (p : (D.obj j).left) = 0) (hR : ∀ j, (p : (D.obj j).right) = 0)
    (c : Cocone D) (hTL : (p : c.pt.left) = 0) (hTR : (p : c.pt.right) = 0)
    (hc : IsColimit c) (j : J) (n : AsSmall.{u} ℕ) :
    colimit.ι ((frobeniusArrowFamilyDiagram D p hp hL hR).flip.obj n) j ≫
      (frobeniusArrowFamilyStageColimitIso D p hp hL hR c hTL hTR hc).hom.app n = c.ι.app j :=
  (colimit.isColimit D).comp_coconePointUniqueUpToIso_hom hc j

end SerrePositivity.AlgebraicGeometry
