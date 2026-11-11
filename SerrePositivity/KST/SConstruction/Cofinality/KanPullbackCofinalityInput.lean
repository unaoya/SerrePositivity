module
public import SerrePositivity.KST.SConstruction.Cofinality.ClosedKernelExInfinityVanishing

/-!
概要：一般の Kan 引き戻しから共終性に必要な次数の群比較へ渡す供給境界。
方針：可縮な角と二次以上が自明な底を入力し、元の第一射影の誘導写像を指定する。
規約：実証明の追加供給を待つ Prop 値の明示入力であり、公理や instance にしない。
使われ方：Sp への一般空間の完全列 API の供給仕様と元の相対四角形の消費。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：可縮な角と一次までの底を持つ Kan 引き戻しの第一射影の群条件。
方針：一般の fiber 比較と完全列を Sp の正本から消費する境界を記述する。
規約：元の指定射・任意基点を保持し、モデル圏の instance 仮定を入力にしない。
使われ方：元の相対 fiber 比較から元の K 群条件へ移る一般供給。 -/
def KanPullbackCofinalityInput : Prop :=
  ∀ {P X E B : SSet.{u}} [KanComplex P] [KanComplex X] [KanComplex E] [KanComplex B]
    (q : P ⟶ X) (s : P ⟶ E) (g : X ⟶ B) (p : E ⟶ B),
    IsPullback q s g p → (SSet.modelCategoryQuillen.J).rlp p →
    (∀ (n : ℕ) (e : E _⦋0⦌), Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy E n e)) →
    (∀ (n : ℕ), 1 < n → ∀ b : B _⦋0⦌, Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy B n b)) →
    ∀ a : P _⦋0⦌,
      Function.Injective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map 1 q (x := a) rfl) ∧
        ∀ n : ℕ, 1 < n →
          Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n q (x := a) rfl)

end SerrePositivity.KST.SConstruction.Cofinality
