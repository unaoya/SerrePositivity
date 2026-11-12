module

public import SerrePositivity.KST.LocalizingInvariants.CompletionZeroComponent
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentLabels

/-!
概要：元の分母 wide 部分複体の各成分で、同じ零分母始域を選ぶ。
方針：成分射の全射性と実零分母から、成分を保つ定値単体の切断を作る。
規約：元の頂点と元の本質像を保ち、retract 閉包には移らない。
使われ方：Sp-7 の全図式収縮の始点と、離散成分への射の切断。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D : SSet.{u}} [Quasicategory C] [Quasicategory D] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable D]
  (f : C ⟶ D) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor f] (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f)
include h

/-- 概要：各成分で選ぶ、同じ成分の全対象への零分母の始域。
方針：成分射の全射性と実零分母から、成分を保つ定値単体の切断を作る。
規約：元の頂点と元の本質像を保ち、retract 閉包には移らない。
使われ方：Sp-7 の全図式収縮の始点と、離散成分への射の切断。 -/
lemma exists_completionComponentSectionVertex
    (c : SSet.π₀ (completionCofiberWide f : SSet.{u})) :
    ∃ z : (completionCofiberWide f : SSet.{u}) _⦋0⦌,
      SSet.π₀.mk z = c ∧
      ∀ y : (completionCofiberWide f : SSet.{u}) _⦋0⦌,
        c = SSet.π₀.mk y → completionZeroTarget f z.val y.val := by
  obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective c
  exact exists_completionComponentZeroVertex f h x

/-- 概要：元の成分ごとに選んだ零分母始域の頂点。
方針：成分射の全射性と実零分母から、成分を保つ定値単体の切断を作る。
規約：元の頂点と元の本質像を保ち、retract 閉包には移らない。
使われ方：Sp-7 の全図式収縮の始点と、離散成分への射の切断。 -/
def completionComponentSectionVertex
    (c : SSet.π₀ (completionCofiberWide f : SSet.{u})) :
    (completionCofiberWide f : SSet.{u}) _⦋0⦌ :=
  Classical.choose (exists_completionComponentSectionVertex f h c)

/-- 概要：選んだ頂点は指定した元の成分に属する。
方針：成分射の全射性と実零分母から、成分を保つ定値単体の切断を作る。
規約：元の頂点と元の本質像を保ち、retract 閉包には移らない。
使われ方：Sp-7 の全図式収縮の始点と、離散成分への射の切断。 -/
lemma completionComponentSectionVertex_component
    (c : SSet.π₀ (completionCofiberWide f : SSet.{u})) :
    SSet.π₀.mk (completionComponentSectionVertex f h c) = c :=
  (Classical.choose_spec (exists_completionComponentSectionVertex f h c)).1

/-- 概要：同じ成分の任意の元の対象への零射は、元の cofiber 分母である。
方針：成分射の全射性と実零分母から、成分を保つ定値単体の切断を作る。
規約：元の頂点と元の本質像を保ち、retract 閉包には移らない。
使われ方：Sp-7 の全図式収縮の始点と、離散成分への射の切断。 -/
lemma completionComponentSectionVertex_zeroTarget
    (y : (completionCofiberWide f : SSet.{u}) _⦋0⦌) :
    completionZeroTarget f
      (completionComponentSectionVertex f h (SSet.π₀.mk y)).val y.val :=
  (Classical.choose_spec
    (exists_completionComponentSectionVertex f h (SSet.π₀.mk y))).2 y rfl

/-- 概要：元の wide 部分複体から離散成分への全単体の射。
方針：成分射の全射性と実零分母から、成分を保つ定値単体の切断を作る。
規約：元の頂点と元の本質像を保ち、retract 閉包には移らない。
使われ方：Sp-7 の全図式収縮の始点と、離散成分への射の切断。 -/
def completionComponentProjection : (completionCofiberWide f : SSet.{u}) ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj (SSet.π₀ (completionCofiberWide f : SSet.{u})) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.componentLabelMap _ id

/-- 概要：元の零分母始域を定値単体として並べた全成分の切断。
方針：成分射の全射性と実零分母から、成分を保つ定値単体の切断を作る。
規約：元の頂点と元の本質像を保ち、retract 閉包には移らない。
使われ方：Sp-7 の全図式収縮の始点と、離散成分への射の切断。 -/
def completionComponentSection :
    (Functor.const SimplexCategoryᵒᵖ).obj (SSet.π₀ (completionCofiberWide f : SSet.{u})) ⟶
      (completionCofiberWide f : SSet.{u}) where
  app n := ↾fun c => (SSet.const (completionComponentSectionVertex f h c)).app n c
  naturality {_ _} φ := by
    apply ConcreteCategory.hom_ext
    intro c
    exact (SSet.const (completionComponentSectionVertex f h c)).naturality_apply φ c

/-- 概要：同じ零分母始域を選ぶ切断は、離散成分への射の厳密な右逆。
方針：成分射の全射性と実零分母から、成分を保つ定値単体の切断を作る。
規約：元の頂点と元の本質像を保ち、retract 閉包には移らない。
使われ方：Sp-7 の全図式収縮の始点と、離散成分への射の切断。 -/
lemma completionComponentSection_projection :
    completionComponentSection f h ≫ completionComponentProjection f = 𝟙 _ := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro c
  change SSet.π₀.mk
    ((completionCofiberWide f : SSet.{u}).map
      (SimplexCategory.const ⦋0⦌ n.unop 0).op
      ((SSet.const (completionComponentSectionVertex f h c)).app _ c)) = c
  rw [← (SSet.const (completionComponentSectionVertex f h c)).naturality_apply]
  simpa using completionComponentSectionVertex_component f h c

end SerrePositivity.KST.LocalizingInvariants
