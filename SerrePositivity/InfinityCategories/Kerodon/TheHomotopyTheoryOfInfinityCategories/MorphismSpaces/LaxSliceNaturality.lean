module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LaxSliceUniversal

/-!
概要：太い slice の普遍性のパラメーターについての自然性。
方針：左端と円柱の入力の自然性を、太い join の普遍性へ移す。
規約：右図式は固定する。
使われ方：Kerodon §4.6.6（Tag 04HY） の関手単体集合の比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：太い slice の左端の入力はパラメーターの射に自然。
方針：零単体の値の一意性と直積の成分で比較する。
規約：K は固定する。
使われ方：Kerodon §4.6.6（Tag 04HY） の普遍性の自然性。 -/
lemma laxSliceLeftInput_naturality {A B : SSet.{u}} (a : A ⟶ B) (K : SSet.{u}) :
    a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSliceLeftInput B K =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSliceLeftInput A K ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[0] : SSet.{u}) K ◁ a) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro x
  have ht : (stdSimplex.isTerminalObj₀.from B).app (Opposite.op ⦋n⦌)
      (a.app (Opposite.op ⦋n⦌) x) = (stdSimplex.isTerminalObj₀.from A).app (Opposite.op ⦋n⦌) x := by
    apply stdSimplex.ext
    intro i
    omega
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl Δ[0] K).app (Opposite.op ⦋n⦌)
    ((stdSimplex.isTerminalObj₀.from B).app (Opposite.op ⦋n⦌) (a.app (Opposite.op ⦋n⦌) x)),
      a.app (Opposite.op ⦋n⦌) x) = _
  rw [ht]
  rfl

/-- 概要：太い slice の円柱の入力はパラメーターの射に自然。
方針：区間と右成分を保ち、零単体の値の一意性で比較する。
規約：K は固定する。
使われ方：Kerodon §4.6.6（Tag 04HY） の普遍性の自然性。 -/
lemma laxSliceCylinderInput_naturality {A B : SSet.{u}} (a : A ⟶ B) (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinderMap a (𝟙 K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSliceCylinderInput B K =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSliceCylinderInput A K ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[0] : SSet.{u}) K ◁ a) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨x, t⟩, k⟩
  have ht : (stdSimplex.isTerminalObj₀.from ((B ⊗ (Δ[1] : SSet.{u})) ⊗ K)).app
      (Opposite.op ⦋n⦌) ((a.app (Opposite.op ⦋n⦌) x, t), k) =
      (stdSimplex.isTerminalObj₀.from ((A ⊗ (Δ[1] : SSet.{u})) ⊗ K)).app
        (Opposite.op ⦋n⦌) ((x, t), k) := by
    apply stdSimplex.ext
    intro i
    omega
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder Δ[0] K).app (Opposite.op ⦋n⦌)
      (((stdSimplex.isTerminalObj₀.from ((B ⊗ (Δ[1] : SSet.{u})) ⊗ K)).app
        (Opposite.op ⦋n⦌) ((a.app (Opposite.op ⦋n⦌) x, t), k), t), k),
        a.app (Opposite.op ⦋n⦌) x) = _
  rw [ht]
  rfl

/-- 概要：太い slice の uncurry はパラメーターの前合成に自然。
方針：太い join の円柱と両因子で比較する。
規約：図式 p を固定する。
使われ方：Kerodon §4.6.6（Tag 04HY） のパラメーター付き比較。 -/
lemma laxSliceUncurry_precomp {A B K X : SSet.{u}} {p : K ⟶ X}
    (a : A ⟶ B) (f : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSlice p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSliceUncurry (a ≫ f) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinMap a (𝟙 K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSliceUncurry f := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin_hom_ext
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSliceUncurry_cylinder, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_map]
    simp only [Category.assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSliceUncurry_cylinder, reassoc_of% laxSliceCylinderInput_naturality]
    rw [uncurry_natural_left]
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSliceUncurry_inl, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_map]
    simp only [Category.assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSliceUncurry_inl, reassoc_of% laxSliceLeftInput_naturality]
    rw [uncurry_natural_left]
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSliceUncurry_fixed, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_map, Category.id_comp,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSliceUncurry_fixed]

/-- 概要：太い slice の射は uncurry した射で決まる。
方針：普遍性の同値の単射性を使う。
規約：右図式は固定する。
使われ方：Kerodon §4.6.6（Tag 04HY） の curry の自然性。 -/
lemma laxSliceUncurry_injective {A K X : SSet.{u}} {p : K ⟶ X} :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSliceUncurry (A := A) (p := p)) := by
  intro f g h
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSliceHomEquiv p A).injective
  exact Subtype.ext h

/-- 概要：太い slice の curry は左因子の射に自然。
方針：uncurry の単射性と前合成の自然性を使う。
規約：図式 p を固定する。
使われ方：Kerodon §4.6.6（Tag 04HY） の普遍性の自然性。 -/
lemma laxSliceCurry_precomp {A B K X : SSet.{u}} {p : K ⟶ X}
    (a : A ⟶ B) (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin B K ⟶ X) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr B K ≫ F = p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSliceCurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinMap a (𝟙 K) ≫ F)
      (by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_map, Category.id_comp, hF]) = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSliceCurry F hF := by
  apply laxSliceUncurry_injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSliceUncurry_curry, laxSliceUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSliceUncurry_curry]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
