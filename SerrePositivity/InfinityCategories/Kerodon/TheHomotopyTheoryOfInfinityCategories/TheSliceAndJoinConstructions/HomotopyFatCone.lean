module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoin
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy

/-!
概要：定値始域からの指定ホモトピーを、同じ頂点と図式を持つ fat join 錐へ移す。
方針：左の零単体を忘れ、右図式と区間の順を戻して円柱を貼る。
規約：元の円柱全体と両端を厳密に保持する。充填性は不要。
使われ方：F1-4 の全切断の恒等射を表す変換の native な錐への実現。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 左の一点を忘れ、fat 錐の円柱を元の図式の円柱へ写す。 -/
def fatConeCylinderProjection (K : SSet.{u}) :
    ((Δ[0] : SSet.{u}) ⊗ Δ[1]) ⊗ K ⟶ K ⊗ Δ[1] :=
  lift (snd _ K) (fst _ K ≫ snd (Δ[0] : SSet.{u}) Δ[1])

/-- 円柱の零端は、右図式の零端への包含。 -/
lemma fatConeCylinderProjection_zero (K : SSet.{u}) :
    (SSet.ι₀ (X := (Δ[0] : SSet.{u})) ▷ K) ≫ fatConeCylinderProjection K =
      snd (Δ[0] : SSet.{u}) K ≫ SSet.ι₀ (X := K) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 円柱の一端は、右図式の一端への包含。 -/
lemma fatConeCylinderProjection_one (K : SSet.{u}) :
    (SSet.ι₁ (X := (Δ[0] : SSet.{u})) ▷ K) ≫ fatConeCylinderProjection K =
      snd (Δ[0] : SSet.{u}) K ≫ SSet.ι₁ (X := K) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 定値始域からの元の変換を、同じ頂点と図式の fat 錐へ移す。 -/
def homotopyFatCone {K X : SSet.{u}} {f : K ⟶ X} {z : X _⦋0⦌}
    (H : SSet.Homotopy (SSet.const z) f) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin Δ[0] K ⟶ X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinDesc (SSet.yonedaEquiv.symm z) f (fatConeCylinderProjection K ≫ H.h) (by
    rw [← Category.assoc, fatConeCylinderProjection_zero, Category.assoc, H.h₀,
      SSet.yonedaEquiv_symm_zero, SSet.comp_const, SSet.comp_const]) (by
    rw [← Category.assoc, fatConeCylinderProjection_one, Category.assoc, H.h₁])

/-- fat 錐の左因子は元の指定頂点。 -/
lemma homotopyFatCone_inl {K X : SSet.{u}} {f : K ⟶ X} {z : X _⦋0⦌}
    (H : SSet.Homotopy (SSet.const z) f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl Δ[0] K ≫ homotopyFatCone H = SSet.yonedaEquiv.symm z :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_desc _ _ _ _ _

/-- fat 錐の右因子は元の図式。 -/
lemma homotopyFatCone_inr {K X : SSet.{u}} {f : K ⟶ X} {z : X _⦋0⦌}
    (H : SSet.Homotopy (SSet.const z) f) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr Δ[0] K ≫ homotopyFatCone H = f :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_desc _ _ _ _ _

/-- fat 錐の円柱は、元の指定ホモトピー全体を回収する。 -/
lemma homotopyFatCone_cylinder {K X : SSet.{u}} {f : K ⟶ X} {z : X _⦋0⦌}
    (H : SSet.Homotopy (SSet.const z) f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder Δ[0] K ≫ homotopyFatCone H = fatConeCylinderProjection K ≫ H.h :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_desc _ _ _ _ _

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
