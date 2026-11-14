module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedConeSectionEquivalence

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseSSetMaps
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
概要：単体集合の引き戻しと ULift の厳密な同型。
方針：型の ULift の極限保存を単体対象の後合成へ移す。
規約：両射と三対象に Kan 性を要求しない。
使われ方：HTT 4.2.4.1、path 置換の全空間と導来 fiber の宇宙の移送。
-/

@[expose] public section
universe u v
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 概要：単体集合の ULift は指定した二射の引き戻しを保存する。
方針：型の極限保存を単体対象の後合成に適用する。
規約：対象と射は元の宇宙 u に置く。
使われ方：標準の引き戻し比較同型の構成。 -/
instance uliftSSetFunctor_preservesPullback {A B C : SSet.{u}} (f : A ⟶ B) (g : C ⟶ B) :
    PreservesLimit (cospan f g) (SSet.uliftFunctor.{v, u}) := by
  change PreservesLimit (cospan f g)
    ((Functor.whiskeringRight SimplexCategoryᵒᵖ (Type u) (Type (max u v))).obj
      CategoryTheory.uliftFunctor.{v, u})
  infer_instance

/-- 概要：引き戻しの ULift は持ち上げた二射の引き戻しと標準的に同型。
方針：極限保存の標準比較同型を使う。
規約：順射は持ち上げた二つの射影による比較射。
使われ方：path 置換の全空間の宇宙の移送。 -/
def uliftPullbackIso {A B C : SSet.{u}} (f : A ⟶ B) (g : C ⟶ B) :
    (SSet.uliftFunctor.{v, u}).obj (pullback f g) ≅
      pullback ((SSet.uliftFunctor.{v, u}).map f) ((SSet.uliftFunctor.{v, u}).map g) :=
  PreservesPullback.iso _ f g

/-- 概要：引き戻しの ULift の同型は第一射影と厳密に可換。
方針：極限保存同型の第一射影の式を使う。
規約：比較の標的の第一射影を使う。
使われ方：path 置換の path 成分の追跡。 -/
lemma uliftPullbackIso_hom_fst {A B C : SSet.{u}} (f : A ⟶ B) (g : C ⟶ B) :
    (uliftPullbackIso.{u, v} f g).hom ≫ pullback.fst _ _ =
      (SSet.uliftFunctor.{v, u}).map (pullback.fst f g) :=
  PreservesPullback.iso_hom_fst _ f g

/-- 概要：引き戻しの ULift の同型は第二射影と厳密に可換。
方針：極限保存同型の第二射影の式を使う。
規約：比較の標的の第二射影を使う。
使われ方：path 置換の元の源成分の追跡。 -/
lemma uliftPullbackIso_hom_snd {A B C : SSet.{u}} (f : A ⟶ B) (g : C ⟶ B) :
    (uliftPullbackIso.{u, v} f g).hom ≫ pullback.snd _ _ =
      (SSet.uliftFunctor.{v, u}).map (pullback.snd f g) :=
  PreservesPullback.iso_hom_snd _ f g

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
