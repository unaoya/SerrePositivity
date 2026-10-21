module
public import SerrePositivity.KST.Spectra.CofiberMappingFamilies

/-! # 全パラメータ cofiber 作用の単位と合成
概要：基点へ降ろした同じ族の単位・合成を、元の族の厳密な等式から反映する。
方針：商の pushout を入力パラメータと tensor し、商射と基点の二脚で検証する。
規約：Kan 性を要求しない。使われ方：元の全零境界商の厳密豊穣作用。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open Spectra

/-- 境界を保つ実作用は、標的の元の境界商で境界全体を基点へ送る。 -/
lemma boundaryFamily_collapse {B X B' Y P : SSet.{u}} (j : B ⟶ X) (j' : B' ⟶ Y)
    (a : X ⊗ P ⟶ Y) (b : B ⊗ P ⟶ B')
    (hb : b ≫ j' = (j ⊗ₘ 𝟙 P) ≫ a) :
    (j ▷ P) ≫ a ≫ PointedObject.cofiberQuotient j' =
      toUnit (B ⊗ P) ≫ (PointedObject.cofiber j').hom := by
  rw [tensorHom_id] at hb
  rw [← Category.assoc, ← hb, Category.assoc, PointedObject.cofiberQuotient_condition,
    comp_toUnit_assoc]

/-- 元の全族の単位作用は、同じ基点付き商でも厳密な単位作用になる。 -/
lemma cofiberFamilyAction_unit {B X P : SSet.{u}} (j : B ⟶ X) (p : 𝟙_ SSet.{u} ⟶ P)
    (a : X ⊗ P ⟶ X)
    (ha : (j ▷ P) ≫ a ≫ PointedObject.cofiberQuotient j =
      toUnit (B ⊗ P) ≫ (PointedObject.cofiber j).hom)
    (h : (𝟙 X ⊗ₘ p) ≫ a = (ρ_ X).hom) :
    (𝟙 (PointedObject.cofiber j).right ⊗ₘ p) ≫
        cofiberFamilyDescRaw j (PointedObject.cofiber j)
          (a ≫ PointedObject.cofiberQuotient j) ha =
      (ρ_ (PointedObject.cofiber j).right).hom := by
  apply ((IsPushout.of_hasPushout j (toUnit B)).map
    ((tensoringRight SSet).obj (𝟙_ SSet.{u}))).hom_ext
  · ext n z
    have hd := types_congr_hom (NatTrans.congr_app
      (cofiberFamilyDescRaw_quotient j _ (a ≫ PointedObject.cofiberQuotient j) ha) n)
      (z.1, p.app n z.2)
    have hh := types_congr_hom (NatTrans.congr_app h n) z
    exact hd.trans (congrArg (fun x => (PointedObject.cofiberQuotient j).app n x) hh)
  · ext n z
    have : Subsingleton ((𝟙_ SSet.{u}).obj n) := by
      change Subsingleton PUnit
      infer_instance
    have hd := types_congr_hom (NatTrans.congr_app
      (cofiberFamilyDescRaw_basepoint j _ (a ≫ PointedObject.cofiberQuotient j) ha) n)
      (z.1, p.app n z.2)
    exact hd.trans (congrArg (fun t => (PointedObject.cofiber j).hom.app n t)
      (Subsingleton.elim _ _))

/-- 元の全族の合成則は、同じ基点付き商でも全パラメータで厳密に成り立つ。 -/
lemma cofiberFamilyAction_comp {B X B' Y B'' Z P R S : SSet.{u}}
    (j : B ⟶ X) (k : B' ⟶ Y) (l : B'' ⟶ Z)
    (a : X ⊗ P ⟶ Y) (b : Y ⊗ R ⟶ Z) (c : X ⊗ S ⟶ Z) (m : P ⊗ R ⟶ S)
    (ha : (j ▷ P) ≫ a ≫ PointedObject.cofiberQuotient k =
      toUnit (B ⊗ P) ≫ (PointedObject.cofiber k).hom)
    (hb : (k ▷ R) ≫ b ≫ PointedObject.cofiberQuotient l =
      toUnit (B' ⊗ R) ≫ (PointedObject.cofiber l).hom)
    (hc : (j ▷ S) ≫ c ≫ PointedObject.cofiberQuotient l =
      toUnit (B ⊗ S) ≫ (PointedObject.cofiber l).hom)
    (h : (a ⊗ₘ 𝟙 R) ≫ b = (α_ X P R).hom ≫ (𝟙 X ⊗ₘ m) ≫ c) :
    (cofiberFamilyDescRaw j (PointedObject.cofiber k)
        (a ≫ PointedObject.cofiberQuotient k) ha ⊗ₘ 𝟙 R) ≫
      cofiberFamilyDescRaw k (PointedObject.cofiber l)
        (b ≫ PointedObject.cofiberQuotient l) hb =
      (α_ (PointedObject.cofiber j).right P R).hom ≫
        (𝟙 _ ⊗ₘ m) ≫ cofiberFamilyDescRaw j (PointedObject.cofiber l)
          (c ≫ PointedObject.cofiberQuotient l) hc := by
  apply (cancel_epi (α_ (PointedObject.cofiber j).right P R).inv).mp
  apply ((IsPushout.of_hasPushout j (toUnit B)).map
    ((tensoringRight SSet).obj (P ⊗ R))).hom_ext
  · ext n z
    have h₁ := types_congr_hom (NatTrans.congr_app
      (cofiberFamilyDescRaw_quotient j _ (a ≫ PointedObject.cofiberQuotient k) ha) n)
      (z.1, z.2.1)
    have h₂ := types_congr_hom (NatTrans.congr_app
      (cofiberFamilyDescRaw_quotient k _ (b ≫ PointedObject.cofiberQuotient l) hb) n)
      (a.app n (z.1, z.2.1), z.2.2)
    have h₃ := types_congr_hom (NatTrans.congr_app
      (cofiberFamilyDescRaw_quotient j _ (c ≫ PointedObject.cofiberQuotient l) hc) n)
      (z.1, m.app n z.2)
    have hh := types_congr_hom (NatTrans.congr_app h n) ((z.1, z.2.1), z.2.2)
    exact (congrArg (fun y => (cofiberFamilyDescRaw k (PointedObject.cofiber l)
      (b ≫ PointedObject.cofiberQuotient l) hb).app n (y, z.2.2)) h₁).trans
        (h₂.trans ((congrArg (fun y => (PointedObject.cofiberQuotient l).app n y) hh).trans
          h₃.symm))
  · ext n z
    have h₁ := types_congr_hom (NatTrans.congr_app
      (cofiberFamilyDescRaw_basepoint j _ (a ≫ PointedObject.cofiberQuotient k) ha) n)
      (z.1, z.2.1)
    have h₂ := types_congr_hom (NatTrans.congr_app
      (cofiberFamilyDescRaw_basepoint k _ (b ≫ PointedObject.cofiberQuotient l) hb) n)
      ((toUnit (𝟙_ SSet.{u} ⊗ P)).app n (z.1, z.2.1), z.2.2)
    have h₃ := types_congr_hom (NatTrans.congr_app
      (cofiberFamilyDescRaw_basepoint j _ (c ≫ PointedObject.cofiberQuotient l) hc) n)
      (z.1, m.app n z.2)
    exact (congrArg (fun y => (cofiberFamilyDescRaw k (PointedObject.cofiber l)
      (b ≫ PointedObject.cofiberQuotient l) hb).app n (y, z.2.2)) h₁).trans
        (h₂.trans h₃.symm)

/-- 通常射での元の作用は、同じ元の商の点つき射として厳密に回収される。 -/
lemma cofiberFamilyAction_hom {B X B' Y P : SSet.{u}} (j : B ⟶ X) (k : B' ⟶ Y)
    (p : 𝟙_ SSet.{u} ⟶ P) (a : X ⊗ P ⟶ Y)
    (ha : (j ▷ P) ≫ a ≫ PointedObject.cofiberQuotient k =
      toUnit (B ⊗ P) ≫ (PointedObject.cofiber k).hom)
    (g : X ⟶ Y) (gQ : PointedObject.cofiber j ⟶ PointedObject.cofiber k)
    (h : (𝟙 X ⊗ₘ p) ≫ a = (ρ_ X).hom ≫ g)
    (hQ : PointedObject.cofiberQuotient j ≫ gQ.right =
      g ≫ PointedObject.cofiberQuotient k) :
    (𝟙 (PointedObject.cofiber j).right ⊗ₘ p) ≫
        cofiberFamilyDescRaw j (PointedObject.cofiber k)
          (a ≫ PointedObject.cofiberQuotient k) ha =
      (ρ_ (PointedObject.cofiber j).right).hom ≫ gQ.right := by
  apply ((IsPushout.of_hasPushout j (toUnit B)).map
    ((tensoringRight SSet).obj (𝟙_ SSet.{u}))).hom_ext
  · ext n z
    have hd := types_congr_hom (NatTrans.congr_app
      (cofiberFamilyDescRaw_quotient j _ (a ≫ PointedObject.cofiberQuotient k) ha) n)
      (z.1, p.app n z.2)
    have hh := types_congr_hom (NatTrans.congr_app h n) z
    have hq := types_congr_hom (NatTrans.congr_app hQ n) z.1
    exact hd.trans ((congrArg (fun x => (PointedObject.cofiberQuotient k).app n x) hh).trans
      hq.symm)
  · ext n z
    have : Subsingleton ((𝟙_ SSet.{u}).obj n) := by
      change Subsingleton PUnit
      infer_instance
    have hd := types_congr_hom (NatTrans.congr_app
      (cofiberFamilyDescRaw_basepoint j _ (a ≫ PointedObject.cofiberQuotient k) ha) n)
      (z.1, p.app n z.2)
    have hw := types_congr_hom (NatTrans.congr_app (Under.w gQ) n) z.1
    exact hd.trans ((congrArg (fun t => (PointedObject.cofiber k).hom.app n t)
      (Subsingleton.elim _ _)).trans hw.symm)

end SerrePositivity.KST.SConstruction
