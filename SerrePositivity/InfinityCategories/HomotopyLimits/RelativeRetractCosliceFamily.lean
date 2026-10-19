module

public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeRightCosliceSection
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialHomEdgeNaturality

/-!
概要：終端部分で同じ図式へ戻る変形に沿って、元の全余錐族を底を保って延長する。
方針：元の族を終端部分と底へ引き戻し、相対 coslice の充填を使う。
規約：両方の指定族を厳密に保持する。使われ方：固定終点根辺円柱の全 Hom 族。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {K L J E B T : SSet.{u}} (q : E ⟶ B) [InnerFibration q]
  (t : K ⟶ E) (W : L ⟶ E) (r : K ⟶ L) (j : J ⟶ K) [Mono j]
  (hj : rightAnodyneExtensions j) (hbase : r ≫ (W ≫ q) = t ≫ q)
  (hterminal : (j ≫ r) ≫ W = j ≫ t) (a : T ⟶ sliceUnder W)

omit [InnerFibration q] [Mono j] in
/-- 終端部分へ制限した元の族と、底に引き戻した元の族は厳密に整合する。 -/
lemma relativeRetractCosliceFamily_compatible :
    (a ≫ normalizedCoconeRestriction W (j ≫ r) hterminal) ≫
        sliceUnderPostcomp (j ≫ t) q =
      ((a ≫ sliceUnderPostcomp W q) ≫
        normalizedCoconeRestriction (W ≫ q) r hbase) ≫
          sliceUnderRestrict (t ≫ q) j := by
  apply sliceUnderUncurry_injective ((j ≫ t) ≫ q)
  rw [sliceUnderUncurry_postcomp, normalizedCoconeRestriction_uncurry,
    sliceUnderUncurry_restrict, normalizedCoconeRestriction_uncurry,
    sliceUnderUncurry_postcomp]
  rw [← Category.assoc (joinMap j (𝟙 T)) (joinMap r (𝟙 T)),
    ← joinMap_comp, Category.comp_id, Category.assoc]

/-- 同じ終端部分と同じ底の族を持つ、全パラメータの実際の延長族。 -/
def relativeRetractCosliceFamily : T ⟶ sliceUnder t :=
  (exists_relativeRightCosliceFamily t q j hj
    (a ≫ normalizedCoconeRestriction W (j ≫ r) hterminal)
    ((a ≫ sliceUnderPostcomp W q) ≫ normalizedCoconeRestriction (W ≫ q) r hbase)
    (relativeRetractCosliceFamily_compatible q t W r j hbase hterminal a)).choose

/-- 終端部分への制限は元の族の同じ引き戻しそのもの。 -/
lemma relativeRetractCosliceFamily_terminal :
    relativeRetractCosliceFamily q t W r j hj hbase hterminal a ≫ sliceUnderRestrict t j =
      a ≫ normalizedCoconeRestriction W (j ≫ r) hterminal :=
  (exists_relativeRightCosliceFamily t q j hj
    (a ≫ normalizedCoconeRestriction W (j ≫ r) hterminal)
    ((a ≫ sliceUnderPostcomp W q) ≫ normalizedCoconeRestriction (W ≫ q) r hbase)
    (relativeRetractCosliceFamily_compatible q t W r j hbase hterminal a)).choose_spec.1

/-- 底の族は元の同じ族を r で引き戻したもの。 -/
lemma relativeRetractCosliceFamily_base :
    relativeRetractCosliceFamily q t W r j hj hbase hterminal a ≫ sliceUnderPostcomp t q =
      (a ≫ sliceUnderPostcomp W q) ≫ normalizedCoconeRestriction (W ≫ q) r hbase :=
  (exists_relativeRightCosliceFamily t q j hj
    (a ≫ normalizedCoconeRestriction W (j ≫ r) hterminal)
    ((a ≫ sliceUnderPostcomp W q) ≫ normalizedCoconeRestriction (W ≫ q) r hbase)
    (relativeRetractCosliceFamily_compatible q t W r j hbase hterminal a)).choose_spec.2

/-- 可変な終点の全族も、元の E 内の族を厳密に保持する。 -/
lemma relativeRetractCosliceFamily_projection :
    relativeRetractCosliceFamily q t W r j hj hbase hterminal a ≫ sliceUnderProjection t =
      a ≫ sliceUnderProjection W := by
  rw [← sliceUnderRestrict_projection t j, ← Category.assoc,
    relativeRetractCosliceFamily_terminal, Category.assoc,
    normalizedCoconeRestriction_projection]

end
end SerrePositivity.InfinityCategories.HomotopyLimits
