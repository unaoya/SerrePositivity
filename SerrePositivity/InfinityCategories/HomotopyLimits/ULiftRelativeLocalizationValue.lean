module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ULiftRelativeLocalization
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagValueRelative
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagValuePostcompose
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagValueTransport

/-!
# 元の Hom の ULift の局所化同値と全語の評価

概要：同じ homEquiv は元の全 zigzag の局所化値を保つ。
方針：元の down・厳密な因子化・全語の評価の合成則を使う。
規約：元の両端の等式移送と元の通常の局所化を保持する。
使われ方：実 DK/Map^h 比較の既存 π₀ 同値への照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.EInfinity.FrameHom.ULiftRelativeLocalization
open CategoryTheory Hammock SimplicialLocalization

lemma homEquiv_value {C : Type u} [Category.{v} C] (W : MorphismProperty C)
    (a : Word) (X Y : ULiftHom.{w} C)
    (S : Zigzag (liftedWeakEquivalences W) a X Y) :
    homEquiv W X Y (Zigzag.Value.value (liftedWeakEquivalences W).Q
        (liftedWeakEquivalences W).Q_inverts S) =
      Zigzag.Value.value W.Q W.Q_inverts (Zigzag.Relative.obj (down W) S) := by
  change eqToHom (Functor.congr_obj (strictLocalizationMap_fac (down W)) X).symm ≫
    (strictLocalizationMap (down W)).map (Zigzag.Value.value (liftedWeakEquivalences W).Q
      (liftedWeakEquivalences W).Q_inverts S) ≫
    eqToHom (Functor.congr_obj (strictLocalizationMap_fac (down W)) Y) = _
  apply eq_of_heq
  simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  exact ((heq_of_eq (Zigzag.Value.value_relative (down W) W.Q W.Q_inverts S)).trans
    ((Zigzag.Value.value_functor_congr (strictLocalizationMap_fac (down W)).symm
      (Zigzag.Value.relativeInverts (down W) W.Q W.Q_inverts)
      (Zigzag.Value.postInverts (liftedWeakEquivalences W).Q
        (liftedWeakEquivalences W).Q_inverts (strictLocalizationMap (down W))) S).trans
      (heq_of_eq (Zigzag.Value.value_postcompose (liftedWeakEquivalences W).Q
        (liftedWeakEquivalences W).Q_inverts (strictLocalizationMap (down W)) S)))).symm
end SerrePositivity.EInfinity.FrameHom.ULiftRelativeLocalization
