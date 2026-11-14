module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Site.CrystallineSiteBasic

/-!
# 結晶厚化の剰余関手

## 概要
分冪厚化の射から剰余環の射を取り、big site の構造射との可換性を示す。

## 方針
分冪射のイデアルの条件から商の射を作り、商写像の全射性で等式を確認する。

## 規約
台環の射の向き。対象の p 冪零性や分冪の一意性は使わない。

## 使われ方
Berthelot III.4、Stacks 07HM。局所化と有限冪商の構造射の照合。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic
namespace CrysOver
variable {p : ℕ} {k : Type u} [CommRing k] {J : Ideal k} {γ : DividedPowers J}
variable {R : Type u} [CommRing R] [Algebra (k ⧸ J) R] {κ : Cardinal.{u}}
variable {X Y Z : CrysOver p γ R κ}

/-- 分冪厚化の射が誘導する剰余環の射。 -/
def Hom.residueMap (f : X ⟶ Y) : X.B ⧸ X.JB →+* Y.B ⧸ Y.JB :=
  Ideal.quotientMap Y.JB f.toAlgHom.toRingHom
    (Ideal.map_le_iff_le_comap.mp f.dp.ideal_comp)

/-- 剰余写像は商の標準写像と可換。 -/
@[simp] theorem Hom.residueMap_mk (f : X ⟶ Y) (b : X.B) :
    f.residueMap (Ideal.Quotient.mk X.JB b) =
      Ideal.Quotient.mk Y.JB (f.toAlgHom b) := rfl

/-- 剰余構造射との可換性を環射の等式として読む。 -/
theorem Hom.residueMap_comp_sec (f : X ⟶ Y) :
    f.residueMap.comp X.sec = Y.sec := by
  ext r
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (X.sec r)
  change f.residueMap (X.sec r) = Y.sec r
  rw [← hb, Hom.residueMap_mk]
  exact f.comm_sec r b hb

/-- 恒等射の剰余写像。 -/
@[simp] theorem Hom.residueMap_id (X : CrysOver p γ R κ) :
    (𝟙 X : X ⟶ X).residueMap = RingHom.id _ := by
  ext b
  rfl

/-- 合成の剰余写像。 -/
@[simp] theorem Hom.residueMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).residueMap = g.residueMap.comp f.residueMap := by
  ext b
  rfl

/-- 基底の p が分冪イデアルに入れば、厚化でも同じことが成り立つ。 -/
theorem prime_mem (X : CrysOver p γ R κ) (hp : (p : k) ∈ J) : (p : X.B) ∈ X.JB := by
  simpa only [map_natCast] using X.base_dp.ideal_comp (Ideal.mem_map_of_mem _ hp)

end CrysOver
end SerrePositivity.BhattScholze.Prismatic
