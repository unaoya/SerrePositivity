module

public import SerrePositivity.InfinityCategories.F1B.KanRelativeInitialPullback
public import SerrePositivity.InfinityCategories.F1B.KanRelativeJoinColimitProjection
public import SerrePositivity.InfinityCategories.F1B.KanRelativeHomLiftingEquiv

/-!
概要：対象の図式の族の各頂点に必要な余極限だけから、普遍な相対 join の図式を構成する。
方針：相対始対象全体からの射を図式の族に沿って引き戻し、切断を uncurry する。
規約：各 fiber の他の図式の余極限は仮定しない。
使われ方：点ごとの余極限の存在からの Kan 拡張の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：指定された族に沿う普遍余錐の射は、必要な点ごとの余極限だけで自明 Kan fibration。
方針：各像の頂点の余極限を相対始対象の逆像へ変換する。
規約：存在条件は図式 b のパラメータ頂点だけについて要求する。
使われ方：普遍余錐の coherent な選択とその一意性。 -/
lemma kanRelativeJoinPointwiseColimitProjection_trivialKanFibration {K C D A : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : K ⟶ C) [CocartesianFibration p]
    (b : A ⟶ kanFiberwiseHom p D)
    (hcol : ∀ a : A _⦋0⦌, ∃ z : JoinCocone
      (kanFiberwiseHomVertexDiagram p (b.app (Opposite.op ⦋0⦌) a)), IsColimitCone z) :
    TrivialKanFibration (pullback.fst b (relativeInitialProjection
      (kanFiberwiseHomPre (D := D) (kanRelativeJoinInlOver p)))) := by
  apply kanRelativeInitialPullback_trivialKanFibration
  intro a
  exact exists_kanRelativeJoin_initial_vertex_of_colimit p _ (hcol a)

/-- 概要：指定した族の各頂点に余極限があれば、相対始対象の族へ持ち上げられる。
方針：各頂点での余極限を一般の相対始対象の族の選択へ渡す。
規約：図式 b の像の外での余極限の存在は不要。
使われ方：実際の相対 join の図式の選択の入力。 -/
lemma exists_kanRelativeJoin_initial_family_of_pointwise_colimits {K C D A : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : K ⟶ C) [CocartesianFibration p]
    (b : A ⟶ kanFiberwiseHom p D)
    (hcol : ∀ a : A _⦋0⦌, ∃ z : JoinCocone
      (kanFiberwiseHomVertexDiagram p (b.app (Opposite.op ⦋0⦌) a)), IsColimitCone z) :
    ∃ l : A ⟶ kanFiberwiseHom (relativeJoinBaseProjection p (𝟙 C)) D,
      l ≫ kanFiberwiseHomPre (D := D) (kanRelativeJoinInlOver p) = b ∧
        ∀ a : A _⦋0⦌, InitialBoundaryLifting
          (kanFiberwiseHomPre (D := D) (kanRelativeJoinInlOver p))
            (l.app (Opposite.op ⦋0⦌) a) := by
  apply exists_kanRelativeInitial_family_of_vertices
  intro a
  exact exists_kanRelativeJoin_initial_vertex_of_colimit p _ (hcol a)

/-- 概要：与えられた図式の各頂点に必要な余極限があれば、普遍な相対 join の図式へ延長できる。
方針：点ごとの仮定から相対始対象の族を作り、制限を保ったまま uncurry する。
規約：底と値域は quasicategory、パラメータは任意。
使われ方：点ごとの余極限からの相対 join の大域的な図式の存在。 -/
lemma exists_kanRelativeJoin_diagram_of_pointwise_colimits {K C D A : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : K ⟶ C) [CocartesianFibration p]
    (c : A ⟶ C) (F : pullback c p ⟶ D)
    (hcol : ∀ a : A _⦋0⦌, ∃ z : JoinCocone
      (kanFiberwiseHomVertexDiagram p
        ((kanFiberwiseHomCurry p c F).app (Opposite.op ⦋0⦌) a)), IsColimitCone z) :
    ∃ H : pullback c (relativeJoinBaseProjection p (𝟙 C)) ⟶ D,
      overPullbackMap (kanRelativeJoinInlOver p) (Over.mk c) ≫ H = F ∧
        ∀ a : A _⦋0⦌, InitialBoundaryLifting
          (kanFiberwiseHomPre (D := D) (kanRelativeJoinInlOver p))
            ((kanFiberwiseHomCurry (relativeJoinBaseProjection p (𝟙 C)) c H).app
              (Opposite.op ⦋0⦌) a) := by
  obtain ⟨l, hl, hli⟩ := exists_kanRelativeJoin_initial_family_of_pointwise_colimits p
    (kanFiberwiseHomCurry p c F) hcol
  have hlp : l ≫ kanFiberwiseHomProjection (relativeJoinBaseProjection p (𝟙 C)) D = c := by
    change l ≫ kanFiberwiseHomProjection (Over.mk (relativeJoinBaseProjection p (𝟙 C))).hom D = c
    rw [← kanFiberwiseHomPre_projection (D := D) (kanRelativeJoinInlOver p),
      ← Category.assoc, hl]
    exact kanFiberwiseHomCurry_projection p c F
  let H := (kanFiberwiseHomEquiv (D := D) (relativeJoinBaseProjection p (𝟙 C)) c).symm ⟨l, hlp⟩
  have hH : kanFiberwiseHomCurry (relativeJoinBaseProjection p (𝟙 C)) c H = l :=
    congrArg Subtype.val ((kanFiberwiseHomEquiv (D := D)
      (relativeJoinBaseProjection p (𝟙 C)) c).apply_symm_apply ⟨l, hlp⟩)
  refine ⟨H, ?_, ?_⟩
  · apply kanFiberwiseHomCurry_injective p c
    erw [kanFiberwiseHomCurry_pre (kanRelativeJoinInlOver p), hH]
    exact hl
  · rw [hH]
    exact hli

end SerrePositivity.InfinityCategories.F1B
