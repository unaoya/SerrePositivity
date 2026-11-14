module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathInnerFibration
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：頂点条件で定義した全部分複体の inner fibration と quasicategory 性。
方針：次元二以上のホーンが全頂点を含むことを使う。
規約：頂点条件の同型不変性は要求しない。
使われ方：Kerodon §4.1.2（Tag 01CD）・5.1.4（Tag 01U9） の cocartesian な coslice。

対応節は Kerodon 4.1（Tag 01B8）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations

/-- 概要：頂点条件で定義した全部分複体の包含は inner fibration。
方針：ホーンに含まれる全頂点の条件を指定された標的の単体へ移す。
規約：元の X の quasicategory 性は不要。
使われ方：Kerodon §4.1.2（Tag 01CD） の全部分圏の相対充填。 -/
@[kerodon 01CW]
instance fullSubcomplexOnVertices_innerFibration (X : SSet.{u}) (P : X _⦋0⦌ → Prop) :
    InnerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι where
  mem := by
    intro A B i hi
    cases hi with
    | @intro n i h0 hn =>
      constructor
      intro a b sq
      have hv : ∀ v : (Δ[n + 2] : SSet.{u}) _⦋0⦌,
          P (b.app (Opposite.op ⦋0⦌) v) := by
        intro v
        let w : (horn (n + 2) i : SSet.{u}) _⦋0⦌ := ⟨v, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertex_mem_horn n i v⟩
        have he := congrArg (fun q ↦ q.app (Opposite.op ⦋0⦌) w) sq.w
        change (a.app (Opposite.op ⦋0⦌) w).val = b.app (Opposite.op ⦋0⦌) v at he
        rw [← he]
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) w)
      refine CommSq.HasLift.mk' {
        l := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift P b hv
        fac_left := ?_
        fac_right := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι P b hv }
      apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι).1
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]
      exact sq.w.symm

/-- 概要：quasicategory の頂点条件で定義した全部分複体は quasicategory。
方針：包含の inner fibration 性を使う。
規約：頂点条件 P は任意。
使われ方：Kerodon §4.1.2（Tag 01CD） の全部分圏、§5.1.4 の輸送の選択。 -/
@[kerodon 01CW]
instance fullSubcomplexOnVertices_quasicategory (X : SSet.{u}) [Quasicategory X]
    (P : X _⦋0⦌ → Prop) : Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) :=
  quasicategory_of_innerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "3.3.3.13" (partial := component) "仮定：準圏 X と頂点条件 P（HA の相対 Alg の全体が準圏という先行結果を用い、P を inert 保存に取る）。結論：頂点条件による充満部分複体が準圏となる（この成分は一致）。O⊗ への categorical fibration 性は型に含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.fullSubcomplexOnVertices_quasicategory
