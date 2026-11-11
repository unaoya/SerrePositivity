module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinInitialBoundary
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.F1BFunctorCategoriesRelativeInitialExtension

/-!
概要：fiber の普遍余錐から相対 join の関手の族の延長を相対骨格で組み立てる。
方針：欠けた単体の最初の頂点の余極限条件を全空間の境界充填へ移す。
規約：部分複体は全頂点を含み、底と標的は quasicategory。
使われ方：Kerodon Lemma 7.3.4.5（Tag 02ZR）–6 の族としての延長の存在。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：fiber の普遍余錐を最初の頂点に持つ部分的な族は全体へ延長できる。
方針：普遍余錐からの相対始点境界充填を相対骨格の延長定理へ渡す。
規約：普遍余錐の表示は欠けた各正次元単体の最初の頂点で指定する。
使われ方：全頂点を含む部分上で既知の Kan 拡張の族を残りの単体へ延長する。 -/
lemma exists_kanRelativeJoin_family_extension_of_colimits {K C D A : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : K ⟶ C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    (A₀ : A.Subcomplex) (hA₀ : ∀ v : A _⦋0⦌, v ∈ A₀.obj (Opposite.op ⦋0⦌))
    (a : (A₀ : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C)) D)
    (b : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHom p D)
    (hw : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomPre (D := D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinInlOver p) = A₀.ι ≫ b)
    (hcol : ∀ (n : ℕ) (σ : A _⦋n + 1⦌), σ ∉ A₀.obj (Opposite.op ⦋n + 1⦌) →
      ∃ (c : C _⦋0⦌) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c ⟶ D) (z : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone d),
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone z ∧
        (((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinCoconeFiberIso p c D).hom.app (Opposite.op ⦋0⦌)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex z.val)).val) =
          a.app (Opposite.op ⦋0⦌) ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex σ, hA₀ _⟩) :
    ∃ l : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C)) D,
      A₀.ι ≫ l = a ∧ l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomPre (D := D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinInlOver p) = b := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.F1BFunctorCategoriesRelativeInitialExtension.exists_lift_of_initial_first_vertices A₀ hA₀
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomPre (D := D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinInlOver p)) a b hw
  intro n σ hσ
  obtain ⟨c, d, z, hz, he⟩ := hcol n σ hσ
  exact he ▸ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinCocone_initialBoundary p c hz

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
