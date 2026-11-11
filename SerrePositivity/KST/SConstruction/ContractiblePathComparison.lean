module
public import SerrePositivity.KST.SConstruction.ContractibleKanTriangles
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.HomotopyCategoryBridge

/-! # 可縮なパラメーター内の指定した道の比較
概要：可縮なパラメーターの辺と指定した辺列のホモトピー圏での一致を証明する。
方針：指定した三辺を回収する実際の三角形を使う。
規約：パラメーターの辺を選び直して結論を弱めない。
使われ方：貼り合わせた自然性と因子の自然性の合成の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 可縮なパラメーターの指定した二つの平行な辺はホモトピー圏で一致する。 -/
lemma contractibleKan_parallel_homMk {P : SSet.{u}} (hP : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan P)
    {x y : P _⦋0⦌} (e f : P.Edge x y) :
    SSet.HomotopyCategory.homMk e = SSet.HomotopyCategory.homMk f := by
  obtain ⟨h⟩ := contractibleKan_nonempty_compStruct hP e (.id y) f
  have hh := SSet.HomotopyCategory.homMk_comp_homMk h
  simpa only [SSet.HomotopyCategory.homMk_id, Category.comp_id] using hh

/-- 可縮なパラメーターの三本の指定した連続辺は同じ端点の指定辺と一致する。 -/
lemma contractibleKan_three_edge_fac {P : SSet.{u}} (hP : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan P)
    {x₀ x₁ x₂ x₃ : P _⦋0⦌} (e₀₁ : P.Edge x₀ x₁) (e₁₂ : P.Edge x₁ x₂)
    (e₂₃ : P.Edge x₂ x₃) (e₀₃ : P.Edge x₀ x₃) :
    (SSet.HomotopyCategory.homMk e₀₁ ≫ SSet.HomotopyCategory.homMk e₁₂) ≫
      SSet.HomotopyCategory.homMk e₂₃ = SSet.HomotopyCategory.homMk e₀₃ := by
  obtain ⟨d⟩ := (hP.isTerminalVertex x₂).nonempty_edge x₀
  let e₀₂ := SSet.Edge.ofTruncated d
  obtain ⟨h₀₁₂⟩ := contractibleKan_nonempty_compStruct hP e₀₁ e₁₂ e₀₂
  obtain ⟨h₀₂₃⟩ := contractibleKan_nonempty_compStruct hP e₀₂ e₂₃ e₀₃
  rw [SSet.HomotopyCategory.homMk_comp_homMk h₀₁₂]
  exact SSet.HomotopyCategory.homMk_comp_homMk h₀₂₃

/-- 同じ可縮なパラメーターの二辺は任意の評価後もホモトピー圏で一致する。 -/
lemma contractibleKan_mapped_parallel_homMk {P K : SSet.{u}} (hP : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan P)
    (F : P ⟶ K) {x y : P _⦋0⦌} (e f : P.Edge x y) :
    SSet.HomotopyCategory.homMk (e.map F) = SSet.HomotopyCategory.homMk (f.map F) :=
  congrArg (SSet.mapHomotopyCategory F).map (contractibleKan_parallel_homMk hP e f)

/-- 可縮なパラメーターの三角形を評価し、指定した実際の三辺を回収する。 -/
lemma contractibleKan_mapped_compStruct {P K : SSet.{u}} (hP : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan P)
    (F : P ⟶ K) {p₀ p₁ p₂ : P _⦋0⦌}
    (a : P.Edge p₀ p₁) (b : P.Edge p₁ p₂) (c : P.Edge p₀ p₂)
    {x₀ x₁ x₂ : K _⦋0⦌} (e : K.Edge x₀ x₁) (f : K.Edge x₁ x₂) (g : K.Edge x₀ x₂)
    (ha : (a.map F).edge = e.edge) (hb : (b.map F).edge = f.edge)
    (hc : (c.map F).edge = g.edge) : Nonempty (SSet.Edge.CompStruct e f g) := by
  obtain ⟨h⟩ := contractibleKan_nonempty_compStruct hP a b c
  exact ⟨(h.map F).ofEq ha hb hc⟩

/-- quasicategory のホモトピー圏の合成等式から指定した三辺の実際の三角形を得る。 -/
lemma nonemptyCompStruct_of_homMk_fac {K : SSet.{u}} [Quasicategory K]
    {x₀ x₁ x₂ : K _⦋0⦌} (e : K.Edge x₀ x₁) (f : K.Edge x₁ x₂) (g : K.Edge x₀ x₂)
    (h : SSet.HomotopyCategory.homMk e ≫ SSet.HomotopyCategory.homMk f =
      SSet.HomotopyCategory.homMk g) : Nonempty (SSet.Edge.CompStruct e f g) := by
  have hh := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory ((truncation 2).obj K)).map h
  rw [CategoryTheory.Functor.map_comp] at hh
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory ((truncation 2).obj K)).map
      (SSet.Truncated.HomotopyCategory.homMk e.toTruncated) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory ((truncation 2).obj K)).map
        (SSet.Truncated.HomotopyCategory.homMk f.toTruncated) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory ((truncation 2).obj K)).map
        (SSet.Truncated.HomotopyCategory.homMk g.toTruncated) at hh
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory, SSet.Truncated.HomotopyCategory.lift_map_homMk] at hh
  exact SSet.Truncated.Edge.CompStruct.nonempty_iff.mpr hh

end SerrePositivity.KST.SConstruction
