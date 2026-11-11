module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.InternalHomSwapNaturality

/-!
概要：二段階の相対内部 Hom の標的の三つの境界成分を比較する。
方針：外側の引き戻しの条件を内側の二射影へ後合成する。
規約：引き戻しの表示と射は任意。
使われ方：相対内部 Hom の二つの制限を交換する標的同型の構成。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：相対内部 Hom の引き戻し条件を標的の任意の射へ後合成する。
方針：引き戻し条件に内部 Hom の作用を合成し、前合成の自然性を使う。
規約：全ての射は任意。
使われ方：入れ子の引き戻しの二成分の整合性。 -/
lemma kanRelativeHomCorner_projection {B₀ B X Y Z : SSet.{u}}
    {j : B₀ ⟶ B} {q : X ⟶ Y} (s : internalHom.PullbackObjObj j q) (r : Y ⟶ Z) :
    s.fst ≫ (ihom B₀).map (q ≫ r) =
      s.snd ≫ (ihom B).map r ≫ (pre j).app Z := by
  rw [Functor.map_comp]
  have h := congrArg (fun z ↦ z ≫ (ihom B₀).map r) s.isPullback.w
  change (s.fst ≫ (ihom B₀).map q) ≫ (ihom B₀).map r =
    (s.snd ≫ (pre j).app Y) ≫ (ihom B₀).map r at h
  simpa only [Category.assoc, ← (pre j).naturality r] using h

variable {A₀ A B₀ B D E : SSet.{u}} {i : A₀ ⟶ A} {j : B₀ ⟶ B} {p : D ⟶ E}

/-- 概要：二段階の相対内部 Hom の二つの部分図式の指定は交わりで一致する。
方針：内側の第一射影へ外側の引き戻し条件を合成する。
規約：最初の制限が i、二番目の制限が j。
使われ方：順序交換の標的の部分図式成分。 -/
lemma kanRelativeHomCorner_diagram (si : internalHom.PullbackObjObj i p)
    (s : internalHom.PullbackObjObj j si.π) :
    s.fst ≫ (ihom B₀).map ((pre i).app D) =
      s.snd ≫ (ihom B).map si.fst ≫ (pre j).app ((ihom A₀).obj D) := by
  have h := kanRelativeHomCorner_projection s si.fst
  have hi : si.π ≫ si.fst = (pre i).app D := si.π_fst
  change s.fst ≫ (ihom B₀).map (si.π ≫ si.fst) =
    s.snd ≫ (ihom B).map si.fst ≫ (pre j).app ((ihom A₀).obj D) at h
  rwa [hi] at h

/-- 概要：部分パラメータ上の図式の像は指定された底の全図式の制限と一致する。
方針：内側の第二射影へ外側の引き戻し条件を合成する。
規約：標的での全図式を保持する。
使われ方：順序交換の標的の底成分。 -/
lemma kanRelativeHomCorner_base (si : internalHom.PullbackObjObj i p)
    (s : internalHom.PullbackObjObj j si.π) :
    s.fst ≫ (ihom B₀).map ((ihom A).map p) =
      s.snd ≫ (ihom B).map si.snd ≫ (pre j).app ((ihom A).obj E) := by
  have h := kanRelativeHomCorner_projection s si.snd
  have hi : si.π ≫ si.snd = (ihom A).map p := si.π_snd
  change s.fst ≫ (ihom B₀).map (si.π ≫ si.snd) =
    s.snd ≫ (ihom B).map si.snd ≫ (pre j).app ((ihom A).obj E) at h
  rwa [hi] at h

/-- 概要：内側の部分図式と底の全図式は、パラメータの族としても整合する。
方針：内側の引き戻し条件を内部 Hom で写す。
規約：外側の第二成分全体で成立する等式。
使われ方：交換後の引き戻しの可換性。 -/
lemma kanRelativeHomCorner_inner (si : internalHom.PullbackObjObj i p)
    (s : internalHom.PullbackObjObj j si.π) :
    s.snd ≫ (ihom B).map si.fst ≫ (ihom B).map ((ihom A₀).map p) =
      s.snd ≫ (ihom B).map si.snd ≫ (ihom B).map ((pre i).app E) := by
  have hi : si.fst ≫ (ihom A₀).map p = si.snd ≫ (pre i).app E := si.isPullback.w
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun z ↦ s.snd ≫ (ihom B).map z) hi

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
