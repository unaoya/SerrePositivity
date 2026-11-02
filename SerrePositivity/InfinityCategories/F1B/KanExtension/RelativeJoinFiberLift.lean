module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinFiberCocone
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinLocalCone
public import SerrePositivity.InfinityCategories.Core.ColimitReindex

/-!
概要：相対 join の fiber の同型を定値な底の係数による標準持ち上げとして同定する。
方針：通常の join への射影と区間・底への二つの射影を比較する。
規約：全ての単体集合を任意とする。
使われ方：局所余錐の比較の終端を実際の fiber の余錐に同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：相対 join の通常の join への射影は区間の時間を保つ。
方針：pullback の条件を区間射影へ後合成する。
規約：二つの構造射は任意。
使われ方：fiber の同型の区間付き係数の計算。 -/
lemma kanRelativeJoin_fst_interval {E F C : SSet.{u}} (p : E ⟶ C) (q : F ⟶ C) :
    pullback.fst (joinMap p q) (joinDiagonal C) ≫ joinIntervalProjection E F =
      pullback.snd (joinMap p q) (joinDiagonal C) ≫ fst Δ[1] C := by
  have h := congrArg (fun z ↦ z ≫ joinIntervalProjection C C)
    (pullback.condition (f := joinMap p q) (g := joinDiagonal C))
  simpa only [Category.assoc, joinIntervalProjection_naturality,
    joinDiagonal_joinIntervalProjection] using h

/-- 概要：fiber の join の同型の通常の join 成分は両端の包含の join。
方針：底変換の標準射の第一射影で、point 上の pullback の同型を消去する。
規約：右端は c を表す零単体。
使われ方：fiber の同型と標準持ち上げの第一成分の一致。 -/
lemma kanRelativeJoinBaseFiberIso_fst {E C : SSet.{u}} (p : E ⟶ C) (c : C _⦋0⦌) :
    (kanRelativeJoinBaseFiberIso p c).hom ≫
      vertexFiberι (relativeJoinBaseProjection p (𝟙 C)) c ≫
        pullback.fst (joinMap p (𝟙 C)) (joinDiagonal C) =
          joinMap (vertexFiberι p c) (SSet.yonedaEquiv.symm c) := by
  rw [← Category.assoc, kanRelativeJoinBaseFiberIso_hom_ι]
  rw [Category.assoc, Category.assoc, relativeJoinPullbackMap_fst,
    ← Category.assoc (inv _) _ _, IsIso.inv_hom_id, Category.id_comp,
    ← joinMap_comp, Category.id_comp]
  rw [IsPullback.isoPullback_hom_fst, SSet.yonedaEquiv_symm_zero]

/-- 概要：fiber の同型の全空間への包含は底に定値な標準相対 join の持ち上げ。
方針：通常の join と区間付き係数の射影を比較する。
規約：定値係数の右端の等式は零単体の標準表示で正規化する。
使われ方：fiber の余錐と局所比較の終端の厳密な同定。 -/
lemma kanRelativeJoinBaseFiberIso_lift {E C : SSet.{u}} (p : E ⟶ C) (c : C _⦋0⦌) :
    (kanRelativeJoinBaseFiberIso p c).hom ≫
      vertexFiberι (relativeJoinBaseProjection p (𝟙 C)) c =
        kanRelativeJoinLift p (𝟙 C) (vertexFiberι p c) (SSet.yonedaEquiv.symm c)
          (SSet.const c) (by rw [SSet.comp_const, vertexFiberι_comp]) (by
            rw [SSet.comp_const, SSet.yonedaEquiv_symm_zero, Category.comp_id]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, kanRelativeJoinBaseFiberIso_fst, kanRelativeJoinLift_fst]
  · rw [Category.assoc, kanRelativeJoinLift_snd]
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst]
      simp only [Category.assoc]
      erw [← kanRelativeJoin_fst_interval,
        reassoc_of% (kanRelativeJoinBaseFiberIso_fst p c), joinIntervalProjection_naturality]
    · rw [Category.assoc, lift_snd]
      change (kanRelativeJoinBaseFiberIso p c).hom ≫
        (vertexFiberι (relativeJoinBaseProjection p (𝟙 C)) c ≫
          relativeJoinBaseProjection p (𝟙 C)) = SSet.const c
      rw [vertexFiberι_comp, SSet.comp_const]

/-- 概要：fiber の余錐を制限した射は定値係数による標準持ち上げに図式を後合成したもの。
方針：fiber の同型の持ち上げ表示と、相対 join の持ち上げの前合成の自然性。
規約：fiber への射 a は任意。
使われ方：局所余錐の比較の終端との同定。 -/
lemma kanRelativeJoinFiberCocone_restrict_val {A E C D : SSet.{u}} (p : E ⟶ C)
    (c : C _⦋0⦌) (H : relativeJoin p (𝟙 C) ⟶ D) (a : A ⟶ vertexFiber p c) :
    ((kanRelativeJoinFiberCocone p c H).restrict a).val =
      kanRelativeJoinLift p (𝟙 C) (a ≫ vertexFiberι p c) (SSet.yonedaEquiv.symm c)
        (SSet.const c) (by rw [SSet.comp_const, Category.assoc, vertexFiberι_comp,
          SSet.comp_const]) (by
            rw [SSet.comp_const, SSet.yonedaEquiv_symm_zero, Category.comp_id]) ≫ H := by
  change joinMap a (𝟙 (Δ[0] : SSet.{u})) ≫ (kanRelativeJoinBaseFiberIso p c).hom ≫
    vertexFiberι (relativeJoinBaseProjection p (𝟙 C)) c ≫ H = _
  rw [← Category.assoc (kanRelativeJoinBaseFiberIso p c).hom _ _,
    kanRelativeJoinBaseFiberIso_lift, ← Category.assoc, kanRelativeJoinLift_precomp]
  simp only [SSet.comp_const, Category.id_comp]

end SerrePositivity.InfinityCategories.F1B
