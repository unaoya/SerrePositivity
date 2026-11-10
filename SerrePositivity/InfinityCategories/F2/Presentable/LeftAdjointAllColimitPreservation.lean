module

public import SerrePositivity.InfinityCategories.F2.Presentable.LeftAdjointCoconePreservation
public import SerrePositivity.InfinityCategories.F2.Presentable.Definition
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：左随伴による任意の小さい形状の余極限の保存。
方針：全パラメータの随伴 Hom 対応で指定余錐の境界充填を移す。
規約：形状の quasicategory 性や標的の余完備性を追加しない。
使われ方：前層反映による native な小余極限構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：左随伴は元の指定 任意の形状の余極限を保存する。
方針：各定値パラメータ族の射の制限を随伴の自然な Hom 全単射で比較する。
規約：同じ全余錐を保持し、図式の置換を要求しない。
使われ方：反映した bar の各項と実現の余極限性。 -/
@[kerodon 02KE]
lemma mapJoinCocone_isColimit_of_adjunction
    {K X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G)
    {p : K ⟶ X} (c : JoinCocone p) (hc : IsColimitCone c) :
    IsColimitCone (mapJoinCocone F c) := by
  apply isColimitCone_of_initialBoundaryLifting_coconeRestriction
  apply initialBoundaryLifting_pre_of_constantFamilyHom
  intro A T
  let aA := postcompositionAdjunction a A
  let δ := joinInl K (Δ[0] : SSet.{u})
  let H := c.val ≫ constantFunctorMap A X
  let V := T ≫ constantFunctorMap A Y
  let R := (hoFunctor.map ((pre δ).app ((ihom A).obj X))).toFunctor
  let S := (hoFunctor.map ((pre δ).app ((ihom A).obj Y))).toFunctor
  have hsource : Function.Bijective (R.map :
      FunctorHom H (V ≫ (ihom A).map G) → _) :=
    homMap_bijective_of_initialBoundaryLifting ((pre δ).app ((ihom A).obj X))
      (functorVertex H) (F1B.isColimitCone_constantFamily c hc).initialBoundaryLifting
      (functorVertex (V ≫ (ihom A).map G))
  let e := parameterUnitHomEquiv aA.unitHom aA.unitMappingSpaceCondition H V
  let e' := parameterUnitHomEquiv aA.unitHom aA.unitMappingSpaceCondition (δ ≫ H) (δ ≫ V)
  have he : (fun α : FunctorHom (H ≫ (ihom A).map F) V ↦ e' (S.map α)) =
      (fun α ↦ R.map (e α)) := by
    funext α
    exact parameterUnitHomMap_precomp aA.unitHom δ H V α
  have hb : Function.Bijective (fun α : FunctorHom (H ≫ (ihom A).map F) V ↦
      e' (S.map α)) := by
    rw [he]
    exact hsource.comp e.bijective
  have hH : H ≫ (ihom A).map F = (mapJoinCocone F c).val ≫ constantFunctorMap A Y := by
    dsimp only [H, mapJoinCocone]
    rw [Category.assoc, constantFunctorMap_postcomp, ← Category.assoc]
  change Function.Bijective (S.map :
    FunctorHom ((mapJoinCocone F c).val ≫ constantFunctorMap A Y) V → _)
  rw [← hH]
  exact hb.of_comp_left e'.injective


/-- 概要：左随伴は全ての小余極限を保存する。
方針：任意の持ち上げた小形状へ一般保存定理を適用する。
規約：標的の余完備性は要求しない。
使われ方：前層反映の全小余極限保存。 -/
@[kerodon 06LC]
lemma adjunction_preservesSmallColimits {X Y : SSet.{u + 1}}
    [Quasicategory X] [Quasicategory Y] {L : X ⟶ Y} {R : Y ⟶ X}
    (a : QCatAdjunction L R) : PreservesSmallColimits L := by
  intro K D c hc
  exact mapJoinCocone_isColimit_of_adjunction a c hc

/-- 概要：可逆な余単位を持つ反映は図式の余極限の存在を戻す。
方針：包含した図式の余極限を反映し、余単位同型で元の図式へ輸送する。
規約：元の形状は任意で、元の図式を結論に保つ。
使われ方：全部分圏の小余極限の構成。 -/
lemma hasColimit_of_reflection {K X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {L : X ⟶ Y} {R : Y ⟶ X}
    (a : QCatAdjunction L R) (e : FunctorIso (R ≫ L) (𝟙 Y))
    (D : K ⟶ Y) (h : HasColimit (D ≫ R)) : HasColimit D := by
  obtain ⟨c, hc⟩ := h
  have hd : HasColimit ((D ≫ R) ≫ L) :=
    ⟨mapJoinCocone L c, mapJoinCocone_isColimit_of_adjunction a c hc⟩
  have ed : FunctorIso ((D ≫ R) ≫ L) D := by
    simpa only [Category.assoc, Category.comp_id] using e.precomp D
  exact (hasColimit_iff_of_functorIso ed).mp hd

/-- 概要：反映は周囲の全小余極限の存在を部分圏へ移す。
方針：同じ元の小図式を包含し、可逆な余単位による構成を使う。
規約：全小余極限の存在を明示入力とする。
使われ方：前層圏の反映模型の余完備性。 -/
lemma hasSmallColimits_of_reflection {X Y : SSet.{u + 1}}
    [Quasicategory X] [Quasicategory Y] {L : X ⟶ Y} {R : Y ⟶ X}
    (a : QCatAdjunction L R) (e : FunctorIso (R ≫ L) (𝟙 Y))
    (hX : HasSmallColimits X) : HasSmallColimits Y := by
  intro K D
  exact hasColimit_of_reflection a e D (hX K (D ≫ R))


end SerrePositivity.InfinityCategories.F2.Presentable
