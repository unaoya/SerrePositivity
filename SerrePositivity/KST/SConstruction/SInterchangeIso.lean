module
public import SerrePositivity.KST.SConstruction.SInterchangeComparison

/-! # 二重 S 構成の厳密な交換同型
概要：全 gapped 図式を保つ転置は二回で恒等となり、S_m(S_n C) と S_n(S_m C) を厳密に同型にする。
方針：二つの単射な包含で内部 Hom の交換の逆律へ帰着する。
規約：零対象の正規化や同値の逆関手の選択を使わない。使われ方：構造射の S₁ 方向の移動。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories

/-- 全 gapped 図式の二重 S 構成を二回転置すると厳密に元へ戻る。 -/
lemma sInterchange_twice (m n : ℕ) (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    sInterchange m n C ≫ sInterchange n m C = 𝟙 _ := by
  let i := (gappedSubcomplex m (sConstruction n C)).ι
  let j := (ihom (arNerve m)).map (gappedSubcomplex n C).ι
  let k := (gappedSubcomplex n (sConstruction m C)).ι
  let l := (ihom (arNerve n)).map (gappedSubcomplex m C).ι
  have : Mono j := (ihom (arNerve m)).map_mono _
  apply inverse_comp_of_commuting_mono (i ≫ j) (k ≫ l)
    (sInterchange m n C) (sInterchange n m C)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso (arNerve m) (arNerve n) C).hom
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso (arNerve n) (arNerve m) C).hom
  · exact (Category.assoc _ _ _).symm.trans (sInterchange_double_ι m n C)
  · exact (Category.assoc _ _ _).symm.trans (sInterchange_double_ι n m C)
  · exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.internalHomSwap_twice _ _ _

/-- 全 gapped 図式の二重 S 構成は二方向の転置で厳密に同型。 -/
def sInterchangeIso (m n : ℕ) (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    sConstruction m (sConstruction n C) ≅ sConstruction n (sConstruction m C) where
  hom := sInterchange m n C
  inv := sInterchange n m C
  hom_inv_id := sInterchange_twice m n C
  inv_hom_id := sInterchange_twice n m C

end SerrePositivity.KST.SConstruction
