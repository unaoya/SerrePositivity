module

public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeRetractCosliceFamily

/-!
概要：図式の切断と収縮に沿い、全余錐族を同じ終端と底のまま戻す。
方針：正規化した制限の uncurry を join の合成へ移す。
規約：底が収縮に沿う定値族である等式を要求する。使われ方：定値な時間図式の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {K L E B T : SSet.{u}} (d : L ⟶ E) (r : K ⟶ L) (s : L ⟶ K)
  (hs : s ≫ r = 𝟙 L)
include hs

/-- 切断で定値な図式を制限すると、元の点図式へ厳密に戻る。 -/
lemma cosliceRetractionFamily_diagram : s ≫ (r ≫ d) = d := by
  rw [← Category.assoc, hs, Category.id_comp]

/-- 元の族を収縮で引き戻し、同じ切断へ戻すと元の全族になる。 -/
lemma cosliceRetractionFamily_section (b : T ⟶ sliceUnder d) :
    (b ≫ sliceUnderRestrict d r) ≫ normalizedCoconeRestriction (r ≫ d) s
        (cosliceRetractionFamily_diagram d r s hs) = b := by
  apply sliceUnderUncurry_injective d
  rw [normalizedCoconeRestriction_uncurry, sliceUnderUncurry_restrict,
    ← Category.assoc, ← joinMap_comp, Category.comp_id, hs,
    joinMap_id, Category.id_comp]

variable (a : T ⟶ sliceUnder (r ≫ d))
local notation "P" => normalizedCoconeRestriction (r ≫ d) s
  (cosliceRetractionFamily_diagram d r s hs)

/-- 指定した切断で全族を読み、その同じ値を収縮で引き戻した族。 -/
def cosliceRetractionFamily : T ⟶ sliceUnder (r ≫ d) :=
  (a ≫ P) ≫ sliceUnderRestrict d r

/-- 引き戻しても、指定した切断上の元の全族を厳密に保持する。 -/
lemma cosliceRetractionFamily_boundary :
    cosliceRetractionFamily d r s hs a ≫ sliceUnderRestrict (r ≫ d) s =
      a ≫ sliceUnderRestrict (r ≫ d) s := by
  apply (cancel_mono (eqToHom (congrArg sliceUnder
    (cosliceRetractionFamily_diagram d r s hs)))).mp
  simpa only [cosliceRetractionFamily, normalizedCoconeRestriction, Category.assoc] using
    (cosliceRetractionFamily_section d r s hs (a ≫ P))

/-- 別の切断へ制限しても、元の指定切断の同じ係数族になる。 -/
lemma cosliceRetractionFamily_other_section (s' : L ⟶ K) (hs' : s' ≫ r = 𝟙 L) :
    cosliceRetractionFamily d r s hs a ≫ normalizedCoconeRestriction (r ≫ d) s'
        (cosliceRetractionFamily_diagram d r s' hs') = a ≫ P :=
  cosliceRetractionFamily_section d r s' hs' (a ≫ P)

/-- 引き戻した族も同じ可変終点の全族を保持する。 -/
lemma cosliceRetractionFamily_projection :
    cosliceRetractionFamily d r s hs a ≫ sliceUnderProjection (r ≫ d) =
      a ≫ sliceUnderProjection (r ≫ d) := by
  rw [← sliceUnderRestrict_projection (r ≫ d) s, ← Category.assoc,
    cosliceRetractionFamily_boundary, Category.assoc, sliceUnderRestrict_projection]

/-- 底が同じ収縮による全族なら、切断からの戻しも底の全族を厳密に保つ。 -/
lemma cosliceRetractionFamily_base (q : E ⟶ B) (b : T ⟶ sliceUnder (d ≫ q))
    (hb : a ≫ sliceUnderPostcomp (r ≫ d) q = b ≫ sliceUnderRestrict (d ≫ q) r) :
    cosliceRetractionFamily d r s hs a ≫ sliceUnderPostcomp (r ≫ d) q =
      a ≫ sliceUnderPostcomp (r ≫ d) q := by
  apply sliceUnderUncurry_injective ((r ≫ d) ≫ q)
  rw [sliceUnderUncurry_postcomp, cosliceRetractionFamily, sliceUnderUncurry_restrict,
    normalizedCoconeRestriction_uncurry, Category.assoc, Category.assoc,
    ← sliceUnderUncurry_postcomp, hb, sliceUnderUncurry_restrict]
  rw [← Category.assoc (joinMap s (𝟙 T)) (joinMap r (𝟙 T)) (sliceUnderUncurry b),
    ← joinMap_comp, Category.comp_id, hs, joinMap_id, Category.id_comp]

end
end SerrePositivity.InfinityCategories.HomotopyLimits
