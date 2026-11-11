module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictNerveMaps
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone
public import Mathlib.CategoryTheory.WithTerminal.Basic

/-!
概要：通常の strict な錐を coherent nerve 上の join の錐にする。
方針：添字圏に始対象を加えた通常の関手を nerve に写し、始対象の標準の錐を制限する。
規約：図式の始域は ULift N(I)、錐は Δ[0]⋆ULift N(I)。頂点は元の錐の頂点と一致する。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6（Tag 03BB） の strict な錐から ∞ 錐への構成。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory Limits SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]

/-- 概要：strict な錐を、持ち上げた添字圏に始対象を加えた関手として表す。
方針：WithInitial.lift に錐の成分と自然性を渡す。
規約：新しい始対象の像は元の錐の頂点。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の通常の錐の図式への読み替え。 -/
def strictConeFunctor {F : I ⥤ C} (c : Cone F) : WithInitial (AsSmall.{v} I) ⥤ C :=
  WithInitial.lift (AsSmall.down ⋙ F) (fun i ↦ c.π.app (AsSmall.down.obj i))
    (fun _ _ f ↦ c.w (AsSmall.down.map f))

/-- 概要：始対象を加えた錐の関手の元の添字圏への制限は元の図式。
方針：WithInitial.lift と包含の対象・射への作用を比較する。
規約：持ち上げた添字圏から元の添字圏へ戻す関手を明示する。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の ∞ 錐の固定図式の条件。 -/
lemma strictConeFunctor_restriction {F : I ⥤ C} (c : Cone F) :
    WithInitial.incl ⋙ strictConeFunctor c = AsSmall.down ⋙ F := by
  rfl

/-- 概要：錐の拡大した関手の新しい始対象での値は元の頂点。
方針：WithInitial.lift の対象部分を評価する。
規約：対象の等号として一致する。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の極限対象との照合。 -/
lemma strictConeFunctor_star {F : I ⥤ C} (c : Cone F) :
    (strictConeFunctor c).obj WithInitial.star = c.pt := rfl

/-- 概要：始対象からの nerve の標準錐の左頂点はその始対象。
方針：coslice の uncurry の固定条件を読む。
規約：左因子は標準零単体。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の strict な錐の頂点の計算。 -/
lemma nerveInitialCone_left {J : Type u} [SmallCategory J] {j : J} (h : IsInitial j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (nerve J) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialCone h = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint j :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_fixed (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialSection h)

variable [SimplicialCategory C]

/-- 概要：strict な錐を表す、join から coherent nerve への射。
方針：始対象を加えた添字圏の始対象錐を元の図式上に制限し、通常の標準 nerve 射で写す。
規約：Hom の宇宙を超える対象の宇宙に合わせ、始域の nerve を明示的に ULift する。
使われ方：HTT 4.2.4.1 の双対の錐 λ̂ の実際の射。 -/
noncomputable def strictCoherentConeMap {F : I ⥤ C} (c : Cone F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{max u v}) ((SSet.uliftFunctor.{v, u}).obj (nerve I)) ⟶
      SimplicialNerve C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.nerveAsSmallIso I).hom ≫ nerveMap WithInitial.incl) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialCone (WithInitial.starInitial (C := AsSmall.{v} I)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.resizedNerveMap (strictConeFunctor c) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C

/-- 概要：strict な錐の coherent 表示は、図式の右因子上で標準の図式に一致する。
方針：始対象錐の右制限の恒等性と拡大した関手の制限を使う。
規約：固定条件は単体集合の射の厳密な等式。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の JoinCone の構成。 -/
lemma strictCoherentConeMap_inr {F : I ⥤ C} (c : Cone F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{max u v}) _ ≫ strictCoherentConeMap c = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{max u v}) (nerve (WithInitial (AsSmall.{v} I))) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialCone (WithInitial.starInitial (C := AsSmall.{v} I)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.resizedNerveMap (strictConeFunctor c) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.resizedNerveMap (strictConeFunctor c) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialCone_inr, Category.id_comp]
  rw [strictCoherentConeMap, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.assoc, h]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.nerveAsSmallIso I).hom ≫ nerveMap WithInitial.incl ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.resizedNerveMap (strictConeFunctor c) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C) = _
  rw [← Category.assoc (nerveMap WithInitial.incl), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.resizedNerveMap_precomp,
    strictConeFunctor_restriction]
  rfl

/-- 概要：strict な錐から coherent nerve の固定図式上の錐を得る。
方針：構成した join の射に図式上の固定条件を添える。
規約：追加の極限性や Kan 性の仮定は定義に置かない。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6（Tag 03BB） の λ̂。 -/
noncomputable def strictCoherentCone {F : I ⥤ C} (c : Cone F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F) :=
  ⟨strictCoherentConeMap c, strictCoherentConeMap_inr c⟩

/-- 概要：strict な錐の coherent 表示の左頂点は元の錐の頂点に一致する。
方針：始対象錐の左制限と標準 nerve 射の零単体の計算を使う。
規約：比較する左制限は Δ[0] からの射。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の極限対象の同定。 -/
lemma strictCoherentConeMap_inl {F : I ⥤ C} (c : Cone F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{max u v}) _ ≫ strictCoherentConeMap c =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex c.pt) := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{max u v}) (nerve (WithInitial (AsSmall.{v} I))) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialCone (WithInitial.starInitial (C := AsSmall.{v} I)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.resizedNerveMap (strictConeFunctor c) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C) =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex c.pt) := by
    rw [← Category.assoc, nerveInitialCone_left]
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.resizedNerveMap (strictConeFunctor c)).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ WithInitial.star)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.resizedNerveMap_vertex, strictConeFunctor_star, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent_vertex]
  rw [strictCoherentConeMap, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp]
  exact h

/-- 概要：coherent な錐の頂点は元の strict な錐の対象の標準頂点。
方針：左制限の公式を零単体の Yoneda 表示に移す。
規約：対象の同値類ではなく頂点の等号。
使われ方：HTT 4.2.4.1 の双対の極限対象の指定。 -/
lemma strictCoherentCone_vertex {F : I ⥤ C} (c : Cone F) :
    (strictCoherentCone c).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex c.pt := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_eq]
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] _ ≫ strictCoherentConeMap c) = _
  rw [strictCoherentConeMap_inl, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
