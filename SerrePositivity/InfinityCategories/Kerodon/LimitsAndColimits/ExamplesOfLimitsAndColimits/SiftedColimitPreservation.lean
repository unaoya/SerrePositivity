module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaPresheafSiftedColimits
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.InitialTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SquareFunctorTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.TrivialFibrationCocone

/-!
概要：元の宇宙 u+1 の関手の、小さい sifted な native 余極限の保存性を定める。
方針：元の指定全余錐の像を量化し、構成済みの P_Σ 余錐とその包含へ適用する。
規約：accessible・presentable の定義を含めない。添字は元の小さい宇宙 u。
使われ方：P_Σ の普遍性における保存関手の全部分 ∞ 圏。

対応節は Kerodon 7.6（Tag 03E8）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits

/-- 元の関手が、全ての小さい sifted な指定 native 余極限を保つ条件。 -/
def PreservesSmallSiftedColimits {X Y : SSet.{u + 1}} (F : X ⟶ Y) : Prop :=
  ∀ (I : SSet.{u}) [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity I]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ X) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D),
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone F c)

/-- 元の標的が、全ての小さい sifted な図式の native 余極限を持つ条件。 -/
def HasSmallSiftedColimits (Y : SSet.{u + 1}) : Prop :=
  ∀ (I : SSet.{u}) [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity I]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ Y), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit D

/-- 同じ全関手同型で移しても、元の小さい sifted 余極限保存性は変わらない。 -/
lemma PreservesSmallSiftedColimits.of_functorIso {X Y : SSet.{u + 1}} [Quasicategory Y]
    {F G : X ⟶ Y} (h : PreservesSmallSiftedColimits F) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) :
    PreservesSmallSiftedColimits G := by
  intro I hS D c hc
  exact (h I D c hc).of_functorIso (e.precomp c.val)

/-- 元の P_Σ は全ての小さい sifted な図式の余極限を持つ。 -/
lemma sigma_hasSmallSiftedColimits (C : SSet.{u}) :
    HasSmallSiftedColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C) := by
  intro I hS D
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheaf_hasColimit_of_sifted D

/-- 元の P_Σ の任意の指定 sifted 余極限余錐を、包含自身が余極限へ送る。 -/
lemma sigmaInclusion_map_isColimit {I C : SSet.{u}} [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity I]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C) c) := by
  let d := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafSiftedColimitCone D
  have hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafSiftedColimitCone_isColimit D
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitConeIso d c hd hc)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp D (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C))
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafSiftedColimitCone_inclusion_isColimit D).of_vertexIso e

/-- 元の P_Σ の包含は、全ての小さい sifted な指定 native 余極限を保つ。 -/
lemma sigmaInclusion_preservesSmallSiftedColimits (C : SSet.{u}) :
    PreservesSmallSiftedColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C) := by
  intro I hS D c hc
  exact sigmaInclusion_map_isColimit D c hc

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.5.8.10" (partial := component) "仮定：有限余積を持つ小準圏 C（HTT と一致）。結論：元の包含の左随伴の存在、Yoneda の同じ因子化と有限余積保存、および PΣ の sifted 余極限閉性という (1) の反射部分・(2)・(4)（一致）。反射の accessibility、任意の随伴との (3) の iff、(6) の compact generation はこの組には含まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.sigmaInclusion_preservesSmallSiftedColimits
attribute [cite HTT "5.5.8.14" (partial := direction) "仮定：有限余積を持つ小 C と PΣ(C) の対象 X（HTT と一致）。結論：実際の Ind(C) 値の全単体的図式と PΣ 内の実現 X が存在し、包含は実現を保つので元の P(C) 内でも同じ表示となる (1)⇒(2)（一致）。任意の P(C) 内の Ind 値表示から X の有限積保存を回収する逆向きはこの型の結論に含まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.sigmaInclusion_preservesSmallSiftedColimits
