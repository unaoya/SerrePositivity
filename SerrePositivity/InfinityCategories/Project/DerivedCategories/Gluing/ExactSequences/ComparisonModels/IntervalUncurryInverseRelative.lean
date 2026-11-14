module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.ArrowHomotopies.IntervalUncurryHomotopyInverse
/-! # 区間評価の実逆は指定入力上の全時間固定を保持する

概要：元区間評価後の比較が指定入力で一定なら、区間写像空間へ戻した比較も同じ入力で一定となる。
方針：実逆の全評価等式と区間 uncurry の単射性で確認する。
規約：相対固定は全時間の等式として保持する。
使われ方：三角形の相対比較を、単位対角閉路の両端固定二次元比較へ移す。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
lemma dgGluingIntervalUncurryHomotopyInverse_fixed {A K Z : SSet.{u}} {x y : Z _⦋0⦌}
    {f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y}
    (H : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry g))
    (hx : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ▷ (Δ[1] : SSet.{u})) ≫ H.h = SSet.const x)
    (hy : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ▷ (Δ[1] : SSet.{u})) ≫ H.h = SSet.const y)
    (k : K ⟶ A)
    (hrel : (((Δ[1] : SSet.{u}) ◁ k) ▷ Δ[1]) ≫ H.h =
      fst (Δ[1] ⊗ K) Δ[1] ≫ (Δ[1] ◁ k) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry g) :
    (k ▷ (Δ[1] : SSet.{u})) ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIntervalUncurryHomotopyInverse H hx hy).h =
      fst K Δ[1] ≫ k ≫ g := by
  have hev : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIntervalUncurryHomotopyInverse H hx hy).h =
      (α_ (Δ[1] : SSet.{u}) A Δ[1]).inv ≫ H.h := by
    have h := congrArg (fun q => (α_ (Δ[1] : SSet.{u}) A Δ[1]).inv ≫ q)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIntervalUncurryHomotopyInverseMap_evaluate H hx hy)
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIntervalUncurryHomotopyInverse, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp] using h
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective x y
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, hev]
  calc
    _ = (α_ (Δ[1] : SSet.{u}) K Δ[1]).inv ≫
        (((Δ[1] : SSet.{u}) ◁ k) ▷ Δ[1]) ≫ H.h := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    _ = _ := by
      rw [hrel]
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
