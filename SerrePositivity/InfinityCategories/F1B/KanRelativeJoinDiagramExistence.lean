module

public import SerrePositivity.InfinityCategories.F1B.KanRelativeJoinColimitProjection
public import SerrePositivity.InfinityCategories.F1B.KanRelativeHomLiftingEquiv

/-!
概要：各 fiber での余極限の存在から、普遍な相対 join の図式の族を任意のパラメータ上で選ぶ。
方針：相対始対象全体からの自明 Kan fibration の切断を使い、族を uncurry する。
規約：各 fiber の全図式の余極限の存在を明示的に仮定する。
使われ方：相対 join を使う Kan 拡張の coherent な存在。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：普遍余錐全体からの切断により、任意の図式の族に相対始対象の族を選べる。
方針：頂点での余極限の存在から自明 Kan fibration の切断を取る。
規約：各 fiber の全図式が余極限を持つことを仮定する。
使われ方：相対 join の大域図式を組み立てるための coherent な族。 -/
lemma exists_kanRelativeJoin_initial_family_of_colimits {K C D A : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : K ⟶ C) [CocartesianFibration p]
    (hcol : ∀ (c : C _⦋0⦌) (d : vertexFiber p c ⟶ D),
      ∃ z : JoinCocone d, IsColimitCone z) (b : A ⟶ kanFiberwiseHom p D) :
    ∃ l : A ⟶ kanFiberwiseHom (relativeJoinBaseProjection p (𝟙 C)) D,
      l ≫ kanFiberwiseHomPre (D := D) (kanRelativeJoinInlOver p) = b ∧
        ∀ a : A _⦋0⦌, InitialBoundaryLifting
          (kanFiberwiseHomPre (D := D) (kanRelativeJoinInlOver p))
            (l.app (Opposite.op ⦋0⦌) a) := by
  let V := kanFiberwiseHomPre (D := D) (kanRelativeJoinInlOver p)
  have : TrivialKanFibration (relativeInitialProjection V) :=
    kanRelativeJoinColimitProjection_trivialKanFibration p hcol
  obtain ⟨s, hs⟩ := trivialKanFibration_exists_section (relativeInitialProjection V)
  refine ⟨b ≫ s ≫ (relativeInitialVertices V).ι, ?_, ?_⟩
  · change b ≫ (s ≫ relativeInitialProjection V) = b
    rw [hs]
    exact Category.comp_id b
  · intro a
    exact fullSubcomplexOnVertices_vertex ((b ≫ s).app (Opposite.op ⦋0⦌) a)

/-- 概要：任意のパラメータ上の図式は、各頂点で相対始対象な相対 join の図式へ延長できる。
方針：相対始対象の族を選び、その射影を復元して実際の図式へ uncurry する。
規約：元の図式を厳密に固定し、普遍性を全てのパラメータ頂点で保証する。
使われ方：相対 join による Kan 拡張の存在の図式側の界面。 -/
lemma exists_kanRelativeJoin_diagram_of_colimits {K C D A : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : K ⟶ C) [CocartesianFibration p]
    (hcol : ∀ (c : C _⦋0⦌) (d : vertexFiber p c ⟶ D),
      ∃ z : JoinCocone d, IsColimitCone z) (c : A ⟶ C) (F : pullback c p ⟶ D) :
    ∃ H : pullback c (relativeJoinBaseProjection p (𝟙 C)) ⟶ D,
      overPullbackMap (kanRelativeJoinInlOver p) (Over.mk c) ≫ H = F ∧
        ∀ a : A _⦋0⦌, InitialBoundaryLifting
          (kanFiberwiseHomPre (D := D) (kanRelativeJoinInlOver p))
            ((kanFiberwiseHomCurry (relativeJoinBaseProjection p (𝟙 C)) c H).app
              (Opposite.op ⦋0⦌) a) := by
  obtain ⟨l, hl, hli⟩ := exists_kanRelativeJoin_initial_family_of_colimits p hcol
    (kanFiberwiseHomCurry p c F)
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
