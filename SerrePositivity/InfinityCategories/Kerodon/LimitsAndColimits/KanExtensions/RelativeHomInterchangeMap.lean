module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeHomCorner

/-!
概要：二段階の相対内部 Hom の順序を交換する標的の比較を構成する。
方針：三つの境界成分を内部 Hom の交換で写し、保存された引き戻しへ合わせる。
規約：全ての引き戻しの表示を任意に選べる。
使われ方：境界を固定する関手の相対余錐条件への移送。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

variable {A₀ A B₀ B D E : SSet.{u}} {i : A₀ ⟶ A} {j : B₀ ⟶ B} {p : D ⟶ E}

/-- 概要：交換後の全パラメータの底成分は交換後の部分パラメータと整合する。
方針：元の底成分の可換性を内部 Hom の交換の自然性で写す。
規約：i の比較の後に j の比較を取った標的から出発する。
使われ方：交換後の第二成分の持ち上げ。 -/
lemma kanRelativeHomInterchangeSnd_square (si : internalHom.PullbackObjObj i p)
    (s : internalHom.PullbackObjObj j si.π) :
    (s.fst ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso B₀ A D).hom) ≫ (ihom A).map ((ihom B₀).map p) =
      (s.snd ≫ (ihom B).map si.snd ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso B A E).hom) ≫
        (ihom A).map ((pre j).app E) := by
  calc
    _ = (s.fst ≫ (ihom B₀).map ((ihom A).map p)) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso B₀ A E).hom := by
      simpa only [Category.assoc] using congrArg (fun z ↦ s.fst ≫ z)
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.internalHomSwap_postcomp B₀ A p).symm
    _ = (s.snd ≫ (ihom B).map si.snd ≫ (pre j).app ((ihom A).obj E)) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso B₀ A E).hom := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeHomCorner_base]
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun z ↦ s.snd ≫ (ihom B).map si.snd ≫ z) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.internalHomSwap_pre_left j A E)

/-- 概要：交換後の第二成分を内部 Hom で保存された引き戻しへ持ち上げる。
方針：部分パラメータ上の図式と、底の全図式を交換して合わせる。
規約：j の相対比較の標的を内部 Hom の値として取る。
使われ方：交換後の外側の比較の標的への射の第二成分。 -/
def kanRelativeHomInterchangeSnd (si : internalHom.PullbackObjObj i p)
    (sj : internalHom.PullbackObjObj j p) (s : internalHom.PullbackObjObj j si.π) :
    s.pt ⟶ (ihom A).obj sj.pt :=
  (sj.isPullback.map (ihom A)).lift
    (s.fst ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso B₀ A D).hom)
    (s.snd ≫ (ihom B).map si.snd ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso B A E).hom)
    (kanRelativeHomInterchangeSnd_square si s)

/-- 概要：交換後の第二成分の部分パラメータへの射影。
方針：引き戻しの持ち上げの第一射影。
規約：厳密な射の等式。
使われ方：交換後の外側の引き戻し条件の確認。 -/
@[reassoc]
lemma kanRelativeHomInterchangeSnd_fst (si : internalHom.PullbackObjObj i p)
    (sj : internalHom.PullbackObjObj j p) (s : internalHom.PullbackObjObj j si.π) :
    kanRelativeHomInterchangeSnd si sj s ≫ (ihom A).map sj.fst =
      s.fst ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso B₀ A D).hom :=
  (sj.isPullback.map (ihom A)).lift_fst _ _ _

/-- 概要：交換後の第二成分の底の全図式への射影。
方針：引き戻しの持ち上げの第二射影。
規約：厳密な射の等式。
使われ方：交換後の外側の引き戻し条件の確認。 -/
@[reassoc]
lemma kanRelativeHomInterchangeSnd_snd (si : internalHom.PullbackObjObj i p)
    (sj : internalHom.PullbackObjObj j p) (s : internalHom.PullbackObjObj j si.π) :
    kanRelativeHomInterchangeSnd si sj s ≫ (ihom A).map sj.snd =
      s.snd ≫ (ihom B).map si.snd ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso B A E).hom :=
  (sj.isPullback.map (ihom A)).lift_snd _ _ _

/-- 概要：交換後の二つの成分は外側の引き戻しの条件を満たす。
方針：内側の二射影で比較し、元の三つの境界成分の整合性を使う。
規約：部分図式と部分パラメータの順序を交換する。
使われ方：交換後の標的への比較射の構成。 -/
lemma kanRelativeHomInterchange_square (si : internalHom.PullbackObjObj i p)
    (sj : internalHom.PullbackObjObj j p) (s : internalHom.PullbackObjObj j si.π) :
    (s.snd ≫ (ihom B).map si.fst ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso B A₀ D).hom) ≫
        (ihom A₀).map sj.π =
      kanRelativeHomInterchangeSnd si sj s ≫ (pre i).app sj.pt := by
  have hpb : IsPullback ((ihom A₀).map sj.fst) ((ihom A₀).map sj.snd)
      ((ihom A₀).map ((ihom B₀).map p)) ((ihom A₀).map ((pre j).app E)) :=
    sj.isPullback.map (ihom A₀)
  apply hpb.hom_ext
  · have hj : sj.π ≫ sj.fst = (pre j).app D := sj.π_fst
    simp only [Category.assoc]
    rw [← Functor.map_comp, hj]
    rw [← (pre i).naturality sj.fst]
    erw [reassoc_of% (kanRelativeHomInterchangeSnd_fst si sj s)]
    have h := congrArg (fun z ↦ z ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso B₀ A₀ D).hom)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeHomCorner_diagram si s)
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso_pre, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.internalHomSwap_pre_left] at h
    exact h.symm
  · have hj : sj.π ≫ sj.snd = (ihom B).map p := sj.π_snd
    simp only [Category.assoc]
    rw [← Functor.map_comp, hj]
    rw [← (pre i).naturality sj.snd]
    erw [reassoc_of% (kanRelativeHomInterchangeSnd_snd si sj s)]
    have h := congrArg (fun z ↦ z ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso B A₀ E).hom)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeHomCorner_inner si s)
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.internalHomSwap_postcomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso_pre] at h
    exact h

/-- 概要：二段階の相対内部 Hom の標的へ順序を交換する比較射。
方針：三つの成分を交換し、二段階の引き戻しの普遍性を使う。
規約：任意の引き戻しの表示で定義する。
使われ方：標的の同型と相対境界充填の移送。 -/
def kanRelativeHomInterchangeMap (si : internalHom.PullbackObjObj i p)
    (sj : internalHom.PullbackObjObj j p) (s : internalHom.PullbackObjObj j si.π)
    (t : internalHom.PullbackObjObj i sj.π) : s.pt ⟶ t.pt :=
  t.isPullback.lift
    (s.snd ≫ (ihom B).map si.fst ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso B A₀ D).hom)
    (kanRelativeHomInterchangeSnd si sj s) (kanRelativeHomInterchange_square si sj s)

/-- 概要：順序交換の比較射の第一成分。
方針：外側の引き戻しの第一射影を計算する。
規約：部分図式の成分を交換した射で表す。
使われ方：交換を二度行ったときの計算。 -/
@[reassoc]
lemma kanRelativeHomInterchangeMap_fst (si : internalHom.PullbackObjObj i p)
    (sj : internalHom.PullbackObjObj j p) (s : internalHom.PullbackObjObj j si.π)
    (t : internalHom.PullbackObjObj i sj.π) :
    kanRelativeHomInterchangeMap si sj s t ≫ t.fst =
      s.snd ≫ (ihom B).map si.fst ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso B A₀ D).hom :=
  t.isPullback.lift_fst _ _ _

/-- 概要：順序交換の比較射の第二成分。
方針：外側の引き戻しの第二射影を計算する。
規約：内側の二つの成分を持ち上げた射となる。
使われ方：交換を二度行ったときの計算。 -/
@[reassoc]
lemma kanRelativeHomInterchangeMap_snd (si : internalHom.PullbackObjObj i p)
    (sj : internalHom.PullbackObjObj j p) (s : internalHom.PullbackObjObj j si.π)
    (t : internalHom.PullbackObjObj i sj.π) :
    kanRelativeHomInterchangeMap si sj s t ≫ t.snd = kanRelativeHomInterchangeSnd si sj s :=
  t.isPullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
