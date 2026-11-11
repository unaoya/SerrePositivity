module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeHomLiftingEquiv
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinFamilyAssembly

/-!
概要：fiber の普遍余錐を用いて相対 join の逆像上の実際の図式を延長する。
方針：図式を族へ移し、相対骨格で延長した後、二つの固定条件を保って戻す。
規約：パラメータは任意の単体集合、底と値域は quasicategory。
使われ方：Kerodon Lemma 7.3.4.5（Tag 02ZR）–6 の図式の延長。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：普遍余錐の頂点条件があれば、元の図式と部分上の図式を同時に保つ延長が存在する。
方針：制限の自然性で族の可換四角形を作り、余極限からの延長を uncurry する。
規約：欠けた各単体の最初の頂点で普遍余錐の表示を指定する。
使われ方：相対 join 上の Kan 拡張を実際の単体集合の射として組み立てる。 -/
lemma exists_kanRelativeJoin_diagram_extension_of_colimits {K C D A : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : K ⟶ C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    (c : A ⟶ C) (A₀ : A.Subcomplex)
    (hA₀ : ∀ v : A _⦋0⦌, v ∈ A₀.obj (Opposite.op ⦋0⦌))
    (F : pullback c p ⟶ D)
    (G : pullback (A₀.ι ≫ c) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C)) ⟶ D)
    (hFG : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map
      (Over.homMk A₀.ι rfl : Over.mk (A₀.ι ≫ c) ⟶ Over.mk c) ≫ F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinInlOver p) (Over.mk (A₀.ι ≫ c)) ≫ G)
    (hcol : ∀ (n : ℕ) (σ : A _⦋n + 1⦌), σ ∉ A₀.obj (Opposite.op ⦋n + 1⦌) →
      ∃ (v : C _⦋0⦌) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p v ⟶ D) (z : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone d),
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone z ∧
        (((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinCoconeFiberIso p v D).hom.app (Opposite.op ⦋0⦌)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex z.val)).val) =
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C)) (A₀.ι ≫ c) G).app
            (Opposite.op ⦋0⦌) ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex σ, hA₀ _⟩) :
    ∃ H : pullback c (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C)) ⟶ D,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinInlOver p) (Over.mk c) ≫ H = F ∧
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C))).map
          (Over.homMk A₀.ι rfl : Over.mk (A₀.ι ≫ c) ⟶ Over.mk c) ≫ H = G := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeHomDiagram_lift_iff (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinInlOver p) A₀.ι c F G).2
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRelativeJoin_family_extension_of_colimits p A₀ hA₀
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C)) (A₀.ι ≫ c) G)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry p c F) ?_ hcol
  erw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFiberwiseHomCurry_pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinInlOver p),
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomCurry_precomp]
  exact congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry p (A₀.ι ≫ c)) hFG.symm

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
