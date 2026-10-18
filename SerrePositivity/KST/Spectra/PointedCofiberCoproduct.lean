module

public import SerrePositivity.KST.Spectra.PointedCofiberUniversal
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
概要：点つき射の余積の cofiber は各 cofiber の余積である。
方針：零合成による降下をセルごとに構成し、商写像と余積の一意性で検査する。
規約：任意の小さい添字集合を許す通常の余積の主張。
使われ方：Goerss–Jardine VIII §1。セルの cofiber の Hom を積に分解する準備。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.KST.Spectra.PointedCofiberCoproduct

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Type u} {A B : S → PointedSimplicialSet.{u}} (i : ∀ s, A s ⟶ B s)

/-- 概要：各 cofiber を余積の射の cofiber へ写す。
方針：標的の余積への包含に商写像を合成し、零合成によって降ろす。
規約：射 i は任意で単射性を要求しない。
使われ方：Goerss–Jardine VIII §1。セルごとの cofiber の標準包含。 -/
def inclusion (s : S) : pointedCofiber (i s) ⟶ pointedCofiber (Limits.Sigma.map i) :=
  pointedCofiberDescOfZero (i s)
    (Limits.Sigma.ι B s ≫ pointedCofiberProjection (Limits.Sigma.map i)) (by
    rw [← Category.assoc, ← Limits.Sigma.ι_map, Category.assoc,
      pointedCofiberProjection_zero, comp_zero])

@[reassoc (attr := simp)]
lemma projection_inclusion (s : S) :
    pointedCofiberProjection (i s) ≫ inclusion i s =
      Limits.Sigma.ι B s ≫ pointedCofiberProjection (Limits.Sigma.map i) :=
  pointedCofiberProjection_descOfZero _ _ _

/-- 概要：各 cofiber から余積の射の cofiber への余錐。
方針：構成した包含を cofan に束ねる。
規約：添字は離散圏として扱う。
使われ方：Goerss–Jardine VIII §1。余積の普遍性の検証の対象。 -/
def cofan : Cofan (fun s ↦ pointedCofiber (i s)) :=
  Cofan.mk (pointedCofiber (Limits.Sigma.map i)) (inclusion i)

def desc (s : Cofan (fun s ↦ pointedCofiber (i s))) : pointedCofiber (Limits.Sigma.map i) ⟶ s.pt :=
  pointedCofiberDescOfZero (Limits.Sigma.map i)
    (Limits.Sigma.desc (fun j ↦ pointedCofiberProjection (i j) ≫ s.inj j)) (by
      apply Limits.Sigma.hom_ext
      intro j
      rw [Limits.Sigma.ι_map_assoc, Limits.Sigma.ι_comp_desc, ← Category.assoc,
        pointedCofiberProjection_zero, zero_comp, comp_zero])

@[reassoc (attr := simp)]
lemma projection_desc (s : Cofan (fun s ↦ pointedCofiber (i s))) :
    pointedCofiberProjection (Limits.Sigma.map i) ≫ desc i s =
      Limits.Sigma.desc (fun j ↦ pointedCofiberProjection (i j) ≫ s.inj j) :=
  pointedCofiberProjection_descOfZero _ _ _

/-- 概要：余積の射の cofiber は各 cofiber の余積である。
方針：各商への前合成と元の余積の一意性で cofan の普遍性を示す。
規約：これは厳密な通常の余極限の結果。
使われ方：Goerss–Jardine VIII §1。境界包含の余積の cofiber の分解。 -/
def isColimit : IsColimit (cofan i) :=
  Cofan.IsColimit.mk _ (desc i)
    (fun s j ↦ by
      apply pointedCofiber_hom_ext (i j)
      change pointedCofiberProjection (i j) ≫ inclusion i j ≫ desc i s = _
      rw [← Category.assoc, projection_inclusion, Category.assoc,
        projection_desc, Limits.Sigma.ι_comp_desc])
    (fun s m hm ↦ by
      change pointedCofiber (Limits.Sigma.map i) ⟶ s.pt at m
      change ∀ j, inclusion i j ≫ m = s.inj j at hm
      apply pointedCofiber_hom_ext (Limits.Sigma.map i)
      apply Limits.Sigma.hom_ext
      intro j
      rw [← Category.assoc, ← projection_inclusion, Category.assoc, hm j,
        projection_desc, Limits.Sigma.ι_comp_desc])

/-- 概要：余積の射の cofiber と各 cofiber の選択された余積の標準同型。
方針：構成した cofan の余極限性から一意な同型を得る。
規約：各 cofiber の包含と可換な同型。
使われ方：Goerss–Jardine VIII §1。セルの Hom の積表示への入力。 -/
def iso : pointedCofiber (Limits.Sigma.map i) ≅ ∐ fun s ↦ pointedCofiber (i s) :=
  (isColimit i).coconePointUniqueUpToIso (coproductIsCoproduct _)

end

end SerrePositivity.KST.Spectra.PointedCofiberCoproduct
