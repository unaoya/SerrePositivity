module

public meta import SerrePositivity.Util.Citation
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
概要：集合値の局所同値を元の層化による同型の逆像として固定する。
方針：HTT 6.2.2.7 の局所化の集合値部分で、Mathlib の同じ層化単位と局所全単射判定を使う。
規約：小さい通常 site の集合値部分。空間値層化との同一視は後続の比較で証明する。
使われ方：離散層化と、局所同値に沿う切断の比較。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C]

/-- 集合値前層の射が、同じ通常の層化で同型になること。drafts の元の定義。
HTT 6.2.2.7 の局所化の集合値部分。 -/
@[cite HTT "6.2.2.7" (partial := special)
  "小さい通常の site の集合値層化で同型になる射の定義に限る。"]
def IsLocalEquivSet (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q) : Prop :=
  CategoryTheory.IsIso ((CategoryTheory.presheafToSheaf J (Type u)).map φ)

/-- 同じ集合値局所同値は、実際の位相に対する局所単射性と局所全射性で判定できる。
Mathlib の通常の層化の局所化と局所全単射の既存の比較を特殊化する。 -/
lemma isLocalEquivSet_iff_locallyBijective (J : GrothendieckTopology C)
    {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q) :
    IsLocalEquivSet J φ ↔
      CategoryTheory.Presheaf.IsLocallyInjective J φ ∧
      CategoryTheory.Presheaf.IsLocallySurjective J φ := by
  unfold IsLocalEquivSet
  rw [← J.W_iff φ, J.W_iff_isLocallyBijective φ]

/-- 元の集合値層化の同じ単位は、元の意味で集合値局所同値となる。 -/
lemma isLocalEquivSet_toSheafify (J : GrothendieckTopology C) (P : Cᵒᵖ ⥤ Type u) :
    IsLocalEquivSet J (CategoryTheory.toSheafify J P) :=
  (J.W_iff _).mp (J.W_toSheafify P)

end SerrePositivity.InfinityCategories.Sheaves
