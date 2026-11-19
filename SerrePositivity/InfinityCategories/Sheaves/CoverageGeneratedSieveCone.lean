module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.CoverageGeneratedSieveInclusion

/-!
概要：篩の包含に沿って元の指定錐を制限すると、小さい篩の指定錐を得る。
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

/-- 篩の包含に沿って元の指定錐を制限すると、小さい篩の指定錐を得る。 -/
@[cite HTT "6.2.2.6" (partial := special) "小さい通常の site の Coverage の篩の比較。"]
lemma coverageGeneratedSieveInclusion_cone :
∀ {C : Type u} [SmallCategory C] {U : C}
 (T S : Sieve U) (h : T ≤ S),
 (sieveCone S).whisker (coverageGeneratedSieveInclusion T S h).op = sieveCone T := by
  intro C hC U T S h
  rfl

end SerrePositivity.InfinityCategories.Sheaves
