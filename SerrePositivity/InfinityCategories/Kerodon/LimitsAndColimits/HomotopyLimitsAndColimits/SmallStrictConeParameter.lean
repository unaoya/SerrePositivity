module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictCones

/-!
概要：strict な錐を、元の小圏に始対象を加えた図式として表示する。
方針：既存の持ち上げた添字の表示と AsSmall の同型を介して厳密に比較する。
規約：新しい添字圏 WithInitial I は元の Hom と同じ宇宙 u に置く。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB） の錐の図式全体上の weighted な比較。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]

/-- 概要：strict な錐を元の添字圏に始対象を加えた小さい図式にする。
方針：元の関手と錐の脚で WithInitial.lift を作る。
規約：始対象の像は c.pt、元の対象での値は F。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の weighted な比較に入力する通常の図式。 -/
def smallStrictConeFunctor {F : I ⥤ C} (c : Cone F) : WithInitial I ⥤ C :=
  WithInitial.lift F (fun i ↦ c.π.app i) (fun _ _ f ↦ c.w f)

/-- 概要：小さい錐の関手を元の添字圏へ制限すると元の図式になる。
方針：WithInitial.lift の定義を計算する。
規約：関手の厳密な等式。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の元の図式上の比較との照合。 -/
lemma smallStrictConeFunctor_restriction {F : I ⥤ C} (c : Cone F) :
    WithInitial.incl ⋙ smallStrictConeFunctor c = F := rfl

/-- 概要：始対象を加える操作と AsSmall による持ち上げの間の関手。
方針：各元の添字を降ろして始対象付きの小圏へ写し、再び全体を持ち上げる。
規約：始域と終域はともにサイズ max u v の小圏。
使われ方：HTT 4.2.4.1 の二つの錐の表示のサイズの整合。 -/
def coneIndexResize (I : Type u) [SmallCategory I] :
    WithInitial (AsSmall.{v} I) ⥤ AsSmall.{v} (WithInitial I) :=
  WithInitial.map AsSmall.down ⋙ AsSmall.up

/-- 概要：小さい錐の関手のサイズを調整すると既存の strict な錐の関手に一致する。
方針：始対象と元の添字、四種類の射で持ち上げと降ろしを計算する。
規約：関手の厳密な等式。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の既存の coherent な錐との照合。 -/
lemma coneIndexResize_functor {F : I ⥤ C} (c : Cone F) :
    coneIndexResize I ⋙ AsSmall.down ⋙ smallStrictConeFunctor c = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictConeFunctor c := by
  refine CategoryTheory.Functor.ext (fun a ↦ by cases a <;> rfl) ?_
  intro a b f
  cases a <;> cases b <;>
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  · rfl
  · exact f.elim
  · rfl
  · rfl

/-- 概要：join による錐の形から、小さい始対象付き添字の nerve の ULift への標準射。
方針：始対象の標準錐と AsSmall の二つの表示を合成する。
規約：右因子は ULift N(I)、左因子は Δ[0]。
使われ方：HTT 4.2.4.1 の錐の図式全体の切断を native な錐の図式へ引き戻す射。 -/
noncomputable def smallStrictConeParameter (I : Type u) [SmallCategory I] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{max u v}) ((SSet.uliftFunctor.{v, u}).obj (nerve I)) ⟶
      (SSet.uliftFunctor.{v, u}).obj (nerve (WithInitial I)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.nerveAsSmallIso I).hom ≫ nerveMap WithInitial.incl) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialCone (WithInitial.starInitial (C := AsSmall.{v} I)) ≫
      nerveMap (coneIndexResize I) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.nerveAsSmallIso (WithInitial I)).inv

/-- 概要：小さい始対象付き添字への錐の標準射は右図式上で通常の包含に一致する。
方針：始対象の標準錐の右制限を除き、AsSmall の作用を各単体で比較する。
規約：全次数での厳密な射の等式。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の weighted な比較の元の図式への制限。 -/
lemma smallStrictConeParameter_inr (I : Type u) [SmallCategory I] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{max u v}) _ ≫ smallStrictConeParameter.{u, v} I =
      (SSet.uliftFunctor.{v, u}).map (nerveMap (WithInitial.incl (C := I))) := by
  rw [smallStrictConeParameter, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap]
  simp only [Category.assoc]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{max u v})
    (nerve (WithInitial (AsSmall.{v} I)))), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialCone_inr, Category.id_comp]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  rfl

/-- 概要：小さい始対象付き添字への標準射の左頂点は新しい始対象。
方針：始対象の標準錐の左制限を使い、AsSmall の作用を零単体で比較する。
規約：標準零単体からの射の厳密な等式。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の引き戻した切断の頂点での評価。 -/
lemma smallStrictConeParameter_inl (I : Type u) [SmallCategory I] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{max u v}) _ ≫ smallStrictConeParameter.{u, v} I =
      SSet.yonedaEquiv.symm (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (WithInitial.star : WithInitial I))) := by
  rw [smallStrictConeParameter, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{max u v})
    (nerve (WithInitial (AsSmall.{v} I)))), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.nerveInitialCone_left]
  apply SSet.yonedaEquiv.injective
  simp only [SSet.yonedaEquiv_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint, Equiv.apply_symm_apply]
  change ULift.up ((ComposableArrows.mk₀ (WithInitial.star : WithInitial (AsSmall.{v} I)) ⋙
    coneIndexResize I) ⋙ AsSmall.down) = ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex WithInitial.star)
  congr 1

variable [SimplicialCategory C]

/-- 概要：小さい錐の図式を標準射で引き戻すと既存の coherent な錐の図式になる。
方針：AsSmall の同型を消去し、通常の関手の厳密な比較を使う。
規約：元の strictCoherentConeMap を変更せず一致を証明する。
使われ方：HTT 4.2.4.1 の錐全体上の豊穣比較から native な切断への実際の引き戻し。 -/
lemma smallStrictConeParameter_diagram {F : I ⥤ C} (c : Cone F) :
    smallStrictConeParameter I ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (smallStrictConeFunctor c) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c).val := by
  unfold smallStrictConeParameter _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (nerveMap (coneIndexResize I)), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.resizedNerveMap_precomp,
    coneIndexResize_functor]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
