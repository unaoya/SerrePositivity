module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.SmallSubcomplexStages
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import Mathlib.Logic.Small.Basic

/-!
概要：小さい指定可逆辺族の逆辺と二つの逆三角形を含む小さい種。
方針：ambient の実逆三角形を一度選び、その生成部分複体の小さい和を取る。
規約：同じ辺と三角形を保持し、部分複体の可逆性を ambient から推測しない。
使われ方：Ind-S (4) の小模型での指定反転条件の保持。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 単体が生成する部分複体は各次数で小さい。 -/
lemma small_ofSimplex {X : SSet.{v}} {n : ℕ} (s : X _⦋n⦌)
    (d : SimplexCategoryᵒᵖ) : Small.{u} ((SSet.Subcomplex.ofSimplex s).obj d) := by
  have hr : SSet.Subcomplex.range (SSet.yonedaEquiv.symm s) =
      SSet.Subcomplex.ofSimplex s := by
    simpa using SSet.Subcomplex.range_eq_ofSimplex (SSet.yonedaEquiv.symm s)
  rw [← hr]
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.small_range.{u, v} (SSet.yonedaEquiv.symm s) d

variable {X : SSet.{v}} [Quasicategory X] {ι : Type w}
    (s : ι → X _⦋1⦌) (hs : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (s i)))

/-- 各指定辺について同じ逆辺と二つの実合成三角形を選ぶ。 -/
def inverseWitness (i : ι) := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge.nonempty_inverse (hs i)).some

/-- 二つの逆三角形の生成部分複体の和。 -/
def inverseWitnessSeed : X.Subcomplex :=
  ⨆ i, SSet.Subcomplex.ofSimplex (inverseWitness s hs i).2.1.simplex ⊔
    SSet.Subcomplex.ofSimplex (inverseWitness s hs i).2.2.simplex

/-- 指定辺が小さい族なら、逆三角形を含めた種も各次数で小さい。 -/
lemma small_inverseWitnessSeed [Small.{u} ι] (d : SimplexCategoryᵒᵖ) :
    Small.{u} ((inverseWitnessSeed s hs).obj d) := by
  have (i : ι) (d : SimplexCategoryᵒᵖ) : Small.{u}
      ((SSet.Subcomplex.ofSimplex (inverseWitness s hs i).2.1.simplex ⊔
        SSet.Subcomplex.ofSimplex (inverseWitness s hs i).2.2.simplex).obj d) := by
    change Small.{u} ↥(((SSet.Subcomplex.ofSimplex
      (inverseWitness s hs i).2.1.simplex).obj d) ∪
      ((SSet.Subcomplex.ofSimplex (inverseWitness s hs i).2.2.simplex).obj d))
    have := small_ofSimplex.{u, v} (inverseWitness s hs i).2.1.simplex d
    have := small_ofSimplex.{u, v} (inverseWitness s hs i).2.2.simplex d
    infer_instance
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.small_iSup.{u, v} _ d

/-- 種には元の指定辺そのものも含まれる。 -/
lemma mem_inverseWitnessSeed (i : ι) : s i ∈ (inverseWitnessSeed s hs).obj
    (Opposite.op ⦋1⦌) := by
  have ht : (inverseWitness s hs i).2.1.simplex ∈
      (inverseWitnessSeed s hs).obj (Opposite.op ⦋2⦌) :=
    (le_iSup_of_le i le_sup_left :
      SSet.Subcomplex.ofSimplex (inverseWitness s hs i).2.1.simplex ≤
        inverseWitnessSeed s hs) _ (SSet.Subcomplex.mem_ofSimplex_obj _)
  have hd : X.δ 2 (inverseWitness s hs i).2.1.simplex = s i :=
    (inverseWitness s hs i).2.1.d₂
  rw [← hd]
  exact (inverseWitnessSeed s hs).map (SimplexCategory.δ 2).op ht

/-- 種を含む部分複体では、元の指定辺が同じ実逆三角形によって可逆。 -/
lemma inverseWitnessSeed_invertible (B : X.Subcomplex)
    (hB : inverseWitnessSeed s hs ≤ B) (i : ι)
    (hi : s i ∈ B.obj (Opposite.op ⦋1⦌)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (X := B.toSSet) ⟨s i, hi⟩) := by
  let g := (inverseWitness s hs i).1
  let t₁ := (inverseWitness s hs i).2.1
  let t₂ := (inverseWitness s hs i).2.2
  have ht₁ : t₁.simplex ∈ B.obj (Opposite.op ⦋2⦌) := by
    apply hB
    exact (le_iSup_of_le i le_sup_left : SSet.Subcomplex.ofSimplex t₁.simplex ≤
      inverseWitnessSeed s hs) _ (SSet.Subcomplex.mem_ofSimplex_obj _)
  have ht₂ : t₂.simplex ∈ B.obj (Opposite.op ⦋2⦌) := by
    apply hB
    exact (le_iSup_of_le i le_sup_right : SSet.Subcomplex.ofSimplex t₂.simplex ≤
      inverseWitnessSeed s hs) _ (SSet.Subcomplex.mem_ofSimplex_obj _)
  have hg : g.edge ∈ B.obj (Opposite.op ⦋1⦌) := by
    rw [← t₁.d₀]
    exact B.map (SimplexCategory.δ 0).op ht₁
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (X := B.toSSet) ⟨s i, hi⟩
  let g' : Truncated.Edge (X := (truncation 2).obj B.toSSet)
      (B.toSSet.δ 0 ⟨s i, hi⟩) (B.toSSet.δ 1 ⟨s i, hi⟩) :=
    ⟨⟨g.edge, hg⟩, Subtype.ext g.src_eq, Subtype.ext g.tgt_eq⟩
  let a : Truncated.Edge.CompStruct e g' (Truncated.Edge.id _) := {
    simplex := ⟨t₁.simplex, ht₁⟩
    d₂ := Subtype.ext t₁.d₂
    d₀ := Subtype.ext t₁.d₀
    d₁ := Subtype.ext t₁.d₁ }
  let b : Truncated.Edge.CompStruct g' e (Truncated.Edge.id _) := {
    simplex := ⟨t₂.simplex, ht₂⟩
    d₂ := Subtype.ext t₂.d₂
    d₀ := Subtype.ext t₂.d₀
    d₁ := Subtype.ext t₂.d₁ }
  exact ⟨⟨Truncated.HomotopyCategory.homMk g',
    by simpa using Truncated.HomotopyCategory.homMk_comp_homMk a,
    by simpa using Truncated.HomotopyCategory.homMk_comp_homMk b⟩⟩

/-- 部分複体内の任意の辺の表示に対して、同じ指定一単体の可逆性を回収する。 -/
lemma inverseWitnessSeed_reflects_edge (B : X.Subcomplex)
    (hB : inverseWitnessSeed s hs ≤ B) (i : ι)
    {x y : B.toSSet _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj B.toSSet) x y)
    (he : e.edge.val = s i) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e := by
  have hi := hB _ (mem_inverseWitnessSeed s hs i)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := e)
    (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (X := B.toSSet) ⟨s i, hi⟩) (Subtype.ext he)).mpr
      (inverseWitnessSeed_invertible s hs B hB i hi)

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
