module

public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightFunctoriality

/-!
# 重み付き実現の元の係数射と Yoneda 拡張の係数射の一致

概要：Hovey §5.4 の実際の重み付き実現の射を同じ Kan 拡張の射で計算する。
方針：実現随伴の各単体の式から Hom の係数自然性を計算する。
規約：既存の mate による射を保持し、モデル構造を仮定しない。
使われ方：忘却後の同じ計算対象と重み付き end の比較の自然性。
-/

@[expose] public section

noncomputable section

universe u v

namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.DiagramModel

variable (K : Type u) [SmallCategory K] {C : Type v} [Category.{u} C]
  [HasColimitsOfSize.{u, u} C] (A : K ⥤ SimplexCategory ⥤ C)
private lemma weightsEquivalenceUnit_app (W : Kᵒᵖ ⥤ SSet.{u}) (k : Kᵒᵖ)
    (n : SimplexCategoryᵒᵖ) (x : (W.obj k).obj n) :
    ((((FrameWeightRealization.weightsEquivalence K).toAdjunction.unit.app W).app k).app n) x =
      x := by
  dsimp [FrameWeightRealization.weightsEquivalence, Equivalence.toAdjunction,
    Equivalence.unit, Equivalence.trans]
  simp [Equivalence.funInvIdAssoc, prodOpEquiv]
  rfl

/-- 概要：重み付き実現随伴の単体の像を元の単位で計算（Hovey §5.4）。
方針：Yoneda 随伴の式と添字同値の単位の計算を使う。
規約：元の単体と実際の Kan 拡張の単位を保持する。
使われ方：実現の係数射と Kan 拡張の射の照合。 -/
lemma realizationHomEquiv_app (W : Kᵒᵖ ⥤ SSet.{u}) (Y : C)
    (f : (FrameWeightRealization.functor K A).obj W ⟶ Y)
    (k : Kᵒᵖ) (n : SimplexCategoryᵒᵖ) (x : (W.obj k).obj n) :
    ((((FrameWeightRealization.adjunction K A).homEquiv W Y f).app k).app n) x =
      (uliftYoneda.{u, u, u}.leftKanExtensionUnit (FrameWeightRealization.source K A)).app
        (k.unop, n.unop) ≫
      (FrameWeightRealization.presheafRealization K A).map (uliftYonedaEquiv.symm x) ≫ f := by
  unfold FrameWeightRealization.adjunction
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  simp only [Equiv.trans_apply]
  rw [(FrameWeightRealization.weightsEquivalence K).toAdjunction.homEquiv_unit]
  change ((((Presheaf.uliftYonedaAdjunction.{0, u, u}
    (FrameWeightRealization.presheafRealization K A)
    (uliftYoneda.{u, u, u}.leftKanExtensionUnit (FrameWeightRealization.source K A))).homEquiv
      ((FrameWeightRealization.weightsEquivalence K).functor.obj W) Y f).app
        (Opposite.op (k.unop, n.unop)))
          (((((FrameWeightRealization.weightsEquivalence K).toAdjunction.unit.app W).app k).app n)
            x)).down = _
  rw [_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightsEquivalenceUnit_app]
  exact congrArg ULift.down (Presheaf.uliftYonedaAdjunction_homEquiv_app.{0, u, u}
    (FrameWeightRealization.presheafRealization K A)
    (uliftYoneda.{u, u, u}.leftKanExtensionUnit (FrameWeightRealization.source K A))
    (P := (FrameWeightRealization.weightsEquivalence K).functor.obj W) f
    (Z := Opposite.op (k.unop, n.unop)) x)
-- 代表射の型の別名を横断して結合則を適用するため、この補題だけで透明性を緩める。
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- 概要：Yoneda 拡張の係数射は重み付き実現随伴と両立（Hovey §5.4）。
方針：各単体で元の Kan 単位と係数自然変換の自然性を合成する。
規約：同じ実現対象と元の係数射を使う。
使われ方：既存の mate による係数射の同定。 -/
lemma realizationHomEquiv_lan_source {B : K ⥤ SimplexCategory ⥤ C} (a : A ⟶ B)
    (W : Kᵒᵖ ⥤ SSet.{u}) (Y : C)
    (f : (FrameWeightRealization.functor K B).obj W ⟶ Y) :
    (FrameWeightRealization.adjunction K A).homEquiv W Y
      (((uliftYoneda.{u, u, u}.lan.map (Functor.uncurry.map a)).app
        ((FrameWeightRealization.weightsEquivalence K).functor.obj W)) ≫ f) =
    (FrameWeightRealization.adjunction K B).homEquiv W Y f ≫
      ((FrameWeightRealization.homFamily K).map a.op).app Y := by
  ext k n x
  change ((((FrameWeightRealization.adjunction K A).homEquiv W Y (_ ≫ f)).app k).app n) x =
    (a.app k.unop).app n.unop ≫
      ((((FrameWeightRealization.adjunction K B).homEquiv W Y f).app k).app n) x
  rw [_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.realizationHomEquiv_app, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.realizationHomEquiv_app]
  let t := uliftYoneda.{u, u, u}.lan.map (Functor.uncurry.map a)
  have hu := congr_app
    (uliftYoneda.{u, u, u}.lanUnit.naturality (Functor.uncurry.map a)) (k.unop, n.unop)
  change (a.app k.unop).app n.unop ≫
    (uliftYoneda.{u, u, u}.leftKanExtensionUnit (FrameWeightRealization.source K B)).app
      (k.unop, n.unop) =
    (uliftYoneda.{u, u, u}.leftKanExtensionUnit (FrameWeightRealization.source K A)).app
      (k.unop, n.unop) ≫
      t.app (uliftYoneda.obj (k.unop, n.unop)) at hu
  let rx : uliftYoneda.{u, u, u}.obj (k.unop, n.unop) ⟶
      (FrameWeightRealization.weightsEquivalence K).functor.obj W := uliftYonedaEquiv.symm x
  have hn := t.naturality rx
  change (FrameWeightRealization.presheafRealization K A).map rx ≫
    t.app ((FrameWeightRealization.weightsEquivalence K).functor.obj W) =
    t.app (uliftYoneda.obj (k.unop, n.unop)) ≫
      (FrameWeightRealization.presheafRealization K B).map rx at hn
  rw [← Category.assoc ((a.app _).app _), hu]
  change (uliftYoneda.{u, u, u}.leftKanExtensionUnit (FrameWeightRealization.source K A)).app
    (k.unop, n.unop) ≫ (FrameWeightRealization.presheafRealization K A).map rx ≫
      t.app ((FrameWeightRealization.weightsEquivalence K).functor.obj W) ≫ f =
    ((uliftYoneda.{u, u, u}.leftKanExtensionUnit (FrameWeightRealization.source K A)).app
      (k.unop, n.unop) ≫ t.app (uliftYoneda.obj (k.unop, n.unop))) ≫
        (FrameWeightRealization.presheafRealization K B).map rx ≫ f
  simpa only [Category.assoc] using congrArg (fun z =>
    (uliftYoneda.{u, u, u}.leftKanExtensionUnit (FrameWeightRealization.source K A)).app
      (k.unop, n.unop) ≫ z ≫ f) hn

/-- 概要：実現の既存の mate の射は同じ Kan 拡張の係数射（Hovey §5.4）。
方針：元の随伴の単射性と両 Hom の計算を使う。
規約：既存の FrameWeightRealization.map を変更しない。
使われ方：底への実現比較の図式自然性。 -/
lemma realizationMap_eq_lan {B : K ⥤ SimplexCategory ⥤ C} (a : A ⟶ B) :
    FrameWeightRealization.map K a =
      Functor.whiskerLeft (FrameWeightRealization.weightsEquivalence K).functor
        (uliftYoneda.{u, u, u}.lan.map (Functor.uncurry.map a)) := by
  apply NatTrans.ext
  funext W
  apply ((FrameWeightRealization.adjunction K A).homEquiv W
    ((FrameWeightRealization.functor K B).obj W)).injective
  have h := FrameWeightRealization.homEquiv_frame_naturality K a W _ (𝟙 _)
  have h' := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.realizationHomEquiv_lan_source K A a W _ (𝟙 _)
  let e := (FrameWeightRealization.adjunction K A).homEquiv W
    ((FrameWeightRealization.functor K B).obj W)
  have h₁ := congrArg e (Category.comp_id ((FrameWeightRealization.map K a).app W))
  have h₂ := congrArg e (Category.comp_id
    ((uliftYoneda.{u, u, u}.lan.map (Functor.uncurry.map a)).app
      ((FrameWeightRealization.weightsEquivalence K).functor.obj W)))
  exact h₁.symm.trans ((h.trans h'.symm).trans h₂)

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
