module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeHomInterchangeIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.InitialBoundaryIso

/-!
概要：相対内部 Hom の二つの順序の比較射を標的の同型で同定する。
方針：始域の交換同型と標的の三成分の式を照合する。
規約：充填条件を同定の仮定に含めない。
使われ方：相対余錐と境界の順序交換で始点境界充填を移す。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

variable {A₀ A B₀ B D E : SSet.{u}} {i : A₀ ⟶ A} {j : B₀ ⟶ B} {p : D ⟶ E}

/-- 概要：始域と標的の順序交換は二つの相対内部 Hom の比較射と可換。
方針：外側と内側の引き戻しの各射影で比較する。
規約：比較射そのものの厳密な等式。
使われ方：二つの順序の相対始点境界充填の同定。 -/
lemma kanRelativeHomInterchange_comparison (si : internalHom.PullbackObjObj i p)
    (sj : internalHom.PullbackObjObj j p) (s : internalHom.PullbackObjObj j si.π)
    (t : internalHom.PullbackObjObj i sj.π) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso B A D).hom ≫ t.π =
      s.π ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeHomInterchangeIso si sj s t).hom := by
  apply t.hom_ext
  · have ht : t.π ≫ t.fst = (pre i).app ((ihom B).obj D) := t.π_fst
    have hs : s.π ≫ s.snd = (ihom B).map si.π := s.π_snd
    have hi : si.π ≫ si.fst = (pre i).app D := si.π_fst
    rw [Category.assoc, ht]
    change _ = s.π ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeHomInterchangeMap si sj s t ≫ t.fst
    erw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeHomInterchangeMap_fst]
    rw [← Category.assoc, hs]
    rw [← Category.assoc, ← Functor.map_comp, hi]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso_pre (A := B) (X := D) i).symm
  · have ht : t.π ≫ t.snd = (ihom A).map sj.π := t.π_snd
    rw [Category.assoc, ht]
    change _ = s.π ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeHomInterchangeMap si sj s t ≫ t.snd
    erw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeHomInterchangeMap_snd]
    have hpb : IsPullback ((ihom A).map sj.fst) ((ihom A).map sj.snd)
        ((ihom A).map ((ihom B₀).map p)) ((ihom A).map ((pre j).app E)) :=
      sj.isPullback.map (ihom A)
    apply hpb.hom_ext
    · have hj : sj.π ≫ sj.fst = (pre j).app D := sj.π_fst
      have hs : s.π ≫ s.fst = (pre j).app ((ihom A).obj D) := s.π_fst
      rw [Category.assoc, Category.assoc, ← Functor.map_comp, hj]
      erw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeHomInterchangeSnd_fst]
      rw [← Category.assoc, hs]
      exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.internalHomSwap_pre_left j A D).symm
    · have hj : sj.π ≫ sj.snd = (ihom B).map p := sj.π_snd
      have hs : s.π ≫ s.snd = (ihom B).map si.π := s.π_snd
      have hi : si.π ≫ si.snd = (ihom A).map p := si.π_snd
      rw [Category.assoc, Category.assoc, ← Functor.map_comp, hj]
      erw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeHomInterchangeSnd_snd]
      rw [← Category.assoc, hs]
      rw [← Category.assoc, ← Functor.map_comp, hi]
      exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.internalHomSwap_postcomp B A p).symm

/-- 概要：相対内部 Hom の順序交換は相対始点境界充填を移す。
方針：始域と標的の可換な同型による移送を適用する。
規約：射の充填性や対象の quasicategory 性は仮定しない。
使われ方：境界を固定する関手 V′ の相対余錐条件への接続。 -/
lemma kanInitialBoundaryLifting_relativeHom_interchange
    (si : internalHom.PullbackObjObj i p) (sj : internalHom.PullbackObjObj j p)
    (s : internalHom.PullbackObjObj j si.π) (t : internalHom.PullbackObjObj i sj.π)
    (x : ((ihom B).obj ((ihom A).obj D)) _⦋0⦌) (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting s.π x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting t.π
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso B A D).hom.app (Opposite.op ⦋0⦌) x) :=
  hx.map_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso B A D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeHomInterchangeIso si sj s t)
    (kanRelativeHomInterchange_comparison si sj s t)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
