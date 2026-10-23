module

public import SerrePositivity.InfinityCategories.F1.Joins.JoinEndpointPullbacks
public import SerrePositivity.InfinityCategories.F1.Joins.RelativeJoin
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingCylinderOverMono

/-!
概要：relative join の因子の包含は区間の端点に沿う pullback。
方針：join の包含の自然性から pullback の正方形を消去し、prism の端点の正方形を貼る。
規約：共通の底 S への二射は任意。
使われ方：Kerodon Construction 5.2.3.1、Theorem 5.2.4.1、両端 fiber の厳密な表示。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：prism の指定端点は区間の指定頂点に沿う第一射影の pullback。
方針：第二射影で持ち上げを作り、第一成分は端点条件、第二成分は恒等式で比較する。
規約：端点 i は零・一の両方を扱う。
使われ方：Kerodon Construction 5.2.3.1、relative join の両端の逆像。 -/
lemma isPullback_prismEndpoint_fst (i : Fin 2) (S : SSet.{u}) :
    IsPullback (prismEndpoint i S) (stdSimplex.isTerminalObj₀.from S) (fst Δ[1] S)
      (SSet.const (stdSimplex.obj₀Equiv.symm i) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) := by
  apply IsPullback.mk'
    (by change SSet.const _ = _; rw [SSet.comp_const])
  · intro T a b h₁ h₂
    simpa only [Category.assoc, prismEndpoint_snd, Category.comp_id] using
      h₁ =≫ snd (Δ[1] : SSet.{u}) S
  · intro T a b h
    refine ⟨a ≫ snd Δ[1] S, ?_, stdSimplex.isTerminalObj₀.hom_ext _ _⟩
    apply CartesianMonoidalCategory.hom_ext
    · change (a ≫ snd Δ[1] S) ≫ SSet.const _ = a ≫ fst Δ[1] S
      rw [SSet.comp_const, h, SSet.comp_const]
    · rw [Category.assoc, prismEndpoint_snd, Category.comp_id]

/-- 概要：relative join の左包含は係数付き区間の始点の pullback。
方針：通常の join の左包含の自然性から relative join の定義の正方形を消去する。
規約：係数の底への射は f。
使われ方：Kerodon Construction 5.2.3.1、零 fiber の pullback を貼る前段階。 -/
lemma relativeJoinInl_prism_isPullback {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    IsPullback (relativeJoinInl f g) f
      (pullback.snd (joinMap f g) (joinDiagonal S)) (prismEndpoint 0 S) := by
  have ht : IsPullback
      (relativeJoinInl f g ≫ pullback.fst (joinMap f g) (joinDiagonal S)) f
      (joinMap f g) (prismEndpoint 0 S ≫ joinDiagonal S) := by
    rw [relativeJoinInl_fst, prismEndpoint_zero_joinDiagonal]
    exact isPullback_joinInl_naturality f g
  exact ht.of_right (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)

/-- 概要：relative join の右包含は係数付き区間の終点の pullback。
方針：通常の join の右包含の自然性から relative join の定義の正方形を消去する。
規約：係数の底への射は g。
使われ方：Kerodon Construction 5.2.3.1、一 fiber の pullback を貼る前段階。 -/
lemma relativeJoinInr_prism_isPullback {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    IsPullback (relativeJoinInr f g) g
      (pullback.snd (joinMap f g) (joinDiagonal S)) (prismEndpoint 1 S) := by
  have ht : IsPullback
      (relativeJoinInr f g ≫ pullback.fst (joinMap f g) (joinDiagonal S)) g
      (joinMap f g) (prismEndpoint 1 S ≫ joinDiagonal S) := by
    rw [relativeJoinInr_fst, prismEndpoint_one_joinDiagonal]
    exact isPullback_joinInr_naturality f g
  exact ht.of_right (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)

/-- 概要：relative join の零 fiber は左因子の pullback 表示を持つ。
方針：左包含の正方形に prism の始点の正方形を貼る。
規約：底への射は標準零単体への唯一の射。
使われ方：Kerodon Construction 5.2.3.1、Theorem 5.2.4.1、零 fiber の同型。 -/
lemma relativeJoinInl_endpoint_isPullback {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    IsPullback (relativeJoinInl f g) (stdSimplex.isTerminalObj₀.from X)
      (relativeJoinProjection f g) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) := by
  have hp := (relativeJoinInl_prism_isPullback f g).paste_vert (isPullback_prismEndpoint_fst 0 S)
  convert hp using 1
  · exact stdSimplex.isTerminalObj₀.hom_ext _ _
  · rfl

/-- 概要：relative join の一 fiber は右因子の pullback 表示を持つ。
方針：右包含の正方形に prism の終点の正方形を貼る。
規約：底への射は標準零単体への唯一の射。
使われ方：Kerodon Construction 5.2.3.1、Theorem 5.2.4.1、一 fiber の同型。 -/
lemma relativeJoinInr_endpoint_isPullback {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    IsPullback (relativeJoinInr f g) (stdSimplex.isTerminalObj₀.from Y)
      (relativeJoinProjection f g) (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
  have hp := (relativeJoinInr_prism_isPullback f g).paste_vert (isPullback_prismEndpoint_fst 1 S)
  convert hp using 1
  · exact stdSimplex.isTerminalObj₀.hom_ext _ _
  · rfl

end SerrePositivity.InfinityCategories
