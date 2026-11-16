module

public import SerrePositivity.InfinityCategories.Sheaves.DescentTopology
public import Mathlib.CategoryTheory.Sites.Coverage

/-!
概要：生成 coverage の篩が全引き戻しで降下する場合、生成位相での元の層条件を得る。
方針：生成位相と coverage の既存の Galois 対応を、同じ降下位相へ適用する。
  文献対応：HTT 6.2.2.6、Kerodon §7.3（Tag 02Y1）の生成被覆族の判定の中間補題。
規約：生成篩そのものの降下だけを入力とする drafts の最終定理ではない。
全引き戻しの条件を明示し、これを省略した最終型への接続は別に証明する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]

/-- 生成被覆篩の全引き戻しでの降下は、生成位相での元の層条件と同値。 -/
lemma isSheaf_toGrothendieck_iff_universallyDescending (K : Coverage C)
    (F : Presheaf C E) :
    IsSheaf K.toGrothendieck F ↔
      ∀ (U : C) (R : Presieve U), R ∈ K.coverings U →
        UniversallyDescendingSieve F (Sieve.generate R) := by
  rw [isSheaf_iff_le_descentTopology]
  constructor
  · intro h U R hR
    exact (mem_descentTopology_iff F (Sieve.generate R)).mp
      (h U (Coverage.Saturate.of U R hR))
  · intro h
    apply ((Coverage.gi C).gc K (descentTopology F)).mpr
    intro U R hR
    exact (mem_descentTopology_iff F (Sieve.generate R)).mpr (h U R hR)

end SerrePositivity.InfinityCategories.Sheaves
