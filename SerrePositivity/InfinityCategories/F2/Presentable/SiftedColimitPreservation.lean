module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaPresheafSiftedColimits
public import SerrePositivity.InfinityCategories.Stable.InitialTransport
public import SerrePositivity.InfinityCategories.F1.SquareFunctorTransport
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationCocone

/-!
概要：元の宇宙 u+1 の関手の、小さい sifted な native 余極限の保存性を定める。
方針：元の指定全余錐の像を量化し、構成済みの P_Σ 余錐とその包含へ適用する。
規約：accessible・presentable の定義を含めない。添字は元の小さい宇宙 u。
使われ方：P_Σ の普遍性における保存関手の全部分 ∞ 圏。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の関手が、全ての小さい sifted な指定 native 余極限を保つ条件。 -/
def PreservesSmallSiftedColimits {X Y : SSet.{u + 1}} (F : X ⟶ Y) : Prop :=
  ∀ (I : SSet.{u}) [IsSiftedInfinity I]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ X) (c : JoinCocone D),
    IsColimitCone c → IsColimitCone (mapJoinCocone F c)

/-- 元の標的が、全ての小さい sifted な図式の native 余極限を持つ条件。 -/
def HasSmallSiftedColimits (Y : SSet.{u + 1}) : Prop :=
  ∀ (I : SSet.{u}) [IsSiftedInfinity I]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ Y), HasColimit D

/-- 同じ全関手同型で移しても、元の小さい sifted 余極限保存性は変わらない。 -/
lemma PreservesSmallSiftedColimits.of_functorIso {X Y : SSet.{u + 1}} [Quasicategory Y]
    {F G : X ⟶ Y} (h : PreservesSmallSiftedColimits F) (e : FunctorIso F G) :
    PreservesSmallSiftedColimits G := by
  intro I hS D c hc
  exact (h I D c hc).of_functorIso (e.precomp c.val)

/-- 元の P_Σ は全ての小さい sifted な図式の余極限を持つ。 -/
lemma sigma_hasSmallSiftedColimits (C : SSet.{u}) :
    HasSmallSiftedColimits (SigmaPresheafInfinity C) := by
  intro I hS D
  exact sigmaPresheaf_hasColimit_of_sifted D

/-- 元の P_Σ の任意の指定 sifted 余極限余錐を、包含自身が余極限へ送る。 -/
lemma sigmaInclusion_map_isColimit {I C : SSet.{u}} [IsSiftedInfinity I]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ SigmaPresheafInfinity C)
    (c : JoinCocone D) (hc : IsColimitCone c) :
    IsColimitCone (mapJoinCocone (sigmaPresheafInfinityInclusion C) c) := by
  let d := sigmaPresheafSiftedColimitCone D
  have hd : IsColimitCone d := sigmaPresheafSiftedColimitCone_isColimit D
  have e := VertexIso.map (colimitConeIso d c hd hc)
    (sliceUnderPostcomp D (sigmaPresheafInfinityInclusion C))
  exact (sigmaPresheafSiftedColimitCone_inclusion_isColimit D).of_vertexIso e

/-- 元の P_Σ の包含は、全ての小さい sifted な指定 native 余極限を保つ。 -/
lemma sigmaInclusion_preservesSmallSiftedColimits (C : SSet.{u}) :
    PreservesSmallSiftedColimits (sigmaPresheafInfinityInclusion C) := by
  intro I hS D c hc
  exact sigmaInclusion_map_isColimit D c hc

end SerrePositivity.InfinityCategories.HomotopyLimits
