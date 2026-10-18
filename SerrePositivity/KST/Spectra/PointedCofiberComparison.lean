module

public import SerrePositivity.KST.Spectra.PointedCofiberUniversal
public import SerrePositivity.KST.Spectra.PointedFiberComparison

/-!
概要：点つき cofiber の可換正方形への関手性と同型の移送。
方針：零合成による降下を用い、商写像で射の等式を検査する。
規約：通常の点つき圏の厳密な正方形を使う。
使われ方：Goerss–Jardine I §7、VIII §1。自由基点追加による余積の比較。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.KST.Spectra.PointedCofiberComparison

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A B A' B' : PointedSimplicialSet.{u}} (p : A ⟶ B) (q : A' ⟶ B')

/-- 概要：可換正方形から cofiber 間の射を構成する。
方針：標的の商写像との合成が始域の射を潰すことを使う。
規約：h は p≫b=a≫q の向き。
使われ方：Goerss–Jardine I §7。cofiber の自然な比較。 -/
def map (a : A ⟶ A') (b : B ⟶ B') (h : p ≫ b = a ≫ q) :
    pointedCofiber p ⟶ pointedCofiber q :=
  pointedCofiberDescOfZero p (b ≫ pointedCofiberProjection q) (by
    rw [← Category.assoc, h, Category.assoc, pointedCofiberProjection_zero, comp_zero])

@[reassoc (attr := simp)]
lemma projection_map (a : A ⟶ A') (b : B ⟶ B') (h : p ≫ b = a ≫ q) :
    pointedCofiberProjection p ≫ map p q a b h = b ≫ pointedCofiberProjection q :=
  pointedCofiberProjection_descOfZero _ _ _

/-- 概要：始域と標的の同型で可換な正方形は cofiber の同型を誘導する。
方針：逆の正方形の降下と商写像に関する一意性で両方向を検査する。
規約：Kan 性や単射性は仮定しない。
使われ方：Goerss–Jardine I §7、VIII §1。余積の模型の間の cofiber の比較。 -/
def iso (a : A ≅ A') (b : B ≅ B') (h : p ≫ b.hom = a.hom ≫ q) :
    pointedCofiber p ≅ pointedCofiber q where
  hom := map p q a.hom b.hom h
  inv := map q p a.inv b.inv (PointedFiberComparison.inverse_square p q a b h)
  hom_inv_id := by
    apply pointedCofiber_hom_ext p
    rw [← Category.assoc, projection_map, Category.assoc, projection_map,
      ← Category.assoc, b.hom_inv_id, Category.id_comp, Category.comp_id]
  inv_hom_id := by
    apply pointedCofiber_hom_ext q
    rw [← Category.assoc, projection_map, Category.assoc, projection_map,
      ← Category.assoc, b.inv_hom_id, Category.id_comp, Category.comp_id]

end

end SerrePositivity.KST.Spectra.PointedCofiberComparison
