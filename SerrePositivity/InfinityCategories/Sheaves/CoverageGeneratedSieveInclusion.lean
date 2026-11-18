module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.NativeSiteDescent

/-!
概要：生成篩を含む篩への包含は、元の Over の対象と射を保つ。
方針：元の篩の所属証明と指定された制限錐を保つ。
  文献対応：HTT 6.2.2.6、通常の小さい site の Coverage の場合。
使われ方：生成篩からの降下の判定。
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

namespace SerrePositivity.InfinityCategories.Sheaves

/-- 生成篩を含む篩への包含は、元の Over の対象と射を保つ。 -/
@[cite HTT "6.2.2.6" (partial := special) "小さい通常の site の Coverage の篩の比較。"]
def coverageGeneratedSieveInclusion :
∀ {C : Type u} [SmallCategory C] {U : C}
 (T S : Sieve U) (h : T ≤ S), sieveCategory T ⥤ sieveCategory S := by
  intro C hC U T S h
  exact
    { obj := fun t => ⟨t.obj, h t.obj.hom t.property⟩
      map := fun f => ⟨f.hom⟩ }

end SerrePositivity.InfinityCategories.Sheaves
