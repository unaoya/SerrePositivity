module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FiberwiseHom
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionLifting

/-!
概要：fiberwise Hom の射影の持ち上げ問題を、逆像上の図式の延長と厳密に同定する。
方針：底を固定した Hom の全単射と、その制限に関する自然性を用いる。
規約：持ち上げの同値は任意の射に成立し、充填性を仮定しない。
使われ方：相対指数の inner fibration 性を逆像の幾何学的な条件から導く。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：底のパラメータの制限は逆像上の図式の curry と可換。
方針：一般の fiberwise Functor の制限の計算則を適用する。
規約：底の射は定値とは限らない。
使われ方：内ホーンや外ホーンの持ち上げ問題の変換。 -/
lemma fiberwiseHomCurry_precomp {K C A B D : SSet.{u}} (p : K ⟶ C)
    (i : A ⟶ B) (b : B ⟶ C) (H : pullback b p ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry p (i ≫ b)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map
        (Over.homMk i rfl : Over.mk (i ≫ b) ⟶ Over.mk b) ≫ H) =
      i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry p b H :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorCurry_precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p) ⟨b, H⟩ i

/-- 概要：底を固定した図式から族への curry は単射。
方針：底を固定した Hom の全単射の単射性。
規約：単体集合パラメータは任意。
使われ方：族の制限の一致を実際の図式の一致へ戻す。 -/
lemma fiberwiseHomCurry_injective {K C A D : SSet.{u}} (p : K ⟶ C) (b : A ⟶ C) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry (D := D) p b) := by
  intro H G h
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomEquiv (D := D) p b).injective
  exact Subtype.ext h

/-- 概要：逆像上の図式の延長と fiberwise Hom の射影の持ち上げは同値。
方針：底を固定した Hom の全単射を両端で使い、curry の自然性で境界条件を照合する。
規約：i の単射性も p の充填性も不要。
使われ方：相対指数のホーン持ち上げを逆像の前合成の全射性へ還元する。 -/
lemma fiberwiseHom_extension_iff {K C A B D : SSet.{u}} (p : K ⟶ C)
    (i : A ⟶ B) (b : B ⟶ C) (H₀ : pullback (i ≫ b) p ⟶ D) :
    (∃ H : pullback b p ⟶ D,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map
        (Over.homMk i rfl : Over.mk (i ≫ b) ⟶ Over.mk b) ≫ H = H₀) ↔
    ∃ f : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHom p D,
      i ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry p (i ≫ b) H₀ ∧
        f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection p D = b := by
  constructor
  · rintro ⟨H, hH⟩
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry p b H, ?_, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry_projection p b H⟩
    rw [← fiberwiseHomCurry_precomp, hH]
  · rintro ⟨f, hfi, hfp⟩
    let H := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomEquiv (D := D) p b).symm ⟨f, hfp⟩
    have hH : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry p b H = f :=
      congrArg Subtype.val ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomEquiv (D := D) p b).apply_symm_apply ⟨f, hfp⟩)
    refine ⟨H, fiberwiseHomCurry_injective p (i ≫ b) ?_⟩
    rw [fiberwiseHomCurry_precomp, hH, hfi]

/-- 概要：任意の可換正方形の持ち上げは対応する逆像上の図式の延長と同値。
方針：境界の族を Hom の全単射で戻し、延長の同値を適用する。
規約：結論は CommSq.HasLift そのもの。
使われ方：射の持ち上げ性の定義との接続。 -/
lemma fiberwiseHom_hasLift_iff {K C A B D : SSet.{u}} (p : K ⟶ C)
    {i : A ⟶ B} {a : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHom p D} {b : B ⟶ C}
    (sq : CommSq a i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection p D) b) :
    sq.HasLift ↔ ∃ H : pullback b p ⟶ D,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map
        (Over.homMk i rfl : Over.mk (i ≫ b) ⟶ Over.mk b) ≫ H =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomEquiv (D := D) p (i ≫ b)).symm ⟨a, sq.w⟩ := by
  let H₀ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomEquiv (D := D) p (i ≫ b)).symm ⟨a, sq.w⟩
  have hH₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry p (i ≫ b) H₀ = a :=
    congrArg Subtype.val
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomEquiv (D := D) p (i ≫ b)).apply_symm_apply ⟨a, sq.w⟩)
  rw [fiberwiseHom_extension_iff]
  rw [hH₀]
  constructor
  · intro h
    exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩
  · rintro ⟨f, hfi, hfp⟩
    exact CommSq.HasLift.mk' { l := f, fac_left := hfi, fac_right := hfp }

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
