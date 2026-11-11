module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeHomInterchangeMap

/-!
概要：二段階の相対内部 Hom の標的の順序交換は同型である。
方針：同じ構成を逆順に適用し、三つの境界成分で二度の交換を消去する。
規約：全ての射と引き戻しの表示は任意。
使われ方：相対余錐と境界の比較の順序交換による普遍性の移送。

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

/-- 概要：相対内部 Hom の標的の順序を二度交換すると恒等射に戻る。
方針：外側と内側の引き戻しの射影で比較し、内部 Hom の交換を二度消去する。
規約：構成した比較射そのものについての等式。
使われ方：逆射を持つ順序交換の同型の構成。 -/
lemma kanRelativeHomInterchangeMap_comp (si : internalHom.PullbackObjObj i p)
    (sj : internalHom.PullbackObjObj j p) (s : internalHom.PullbackObjObj j si.π)
    (t : internalHom.PullbackObjObj i sj.π) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeHomInterchangeMap si sj s t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeHomInterchangeMap sj si t s = 𝟙 s.pt := by
  apply s.hom_ext
  · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeHomInterchangeMap_fst,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeHomInterchangeMap_snd_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeHomInterchangeSnd_fst_assoc,
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.internalHomSwap_hom_hom, Category.id_comp]
    rfl
  · have hpb : IsPullback ((ihom B).map si.fst) ((ihom B).map si.snd)
        ((ihom B).map ((ihom A₀).map p)) ((ihom B).map ((pre i).app E)) :=
      si.isPullback.map (ihom B)
    apply hpb.hom_ext
    · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeHomInterchangeMap_snd_assoc,
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeHomInterchangeSnd_fst,
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeHomInterchangeMap_fst_assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.internalHomSwap_hom_hom,
        Category.id_comp]
      rfl
    · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeHomInterchangeMap_snd_assoc,
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeHomInterchangeSnd_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeHomInterchangeSnd_snd_assoc,
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeHomInterchangeMap_snd, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.internalHomSwap_hom_hom,
        Category.id_comp]
      rfl

/-- 概要：二段階の相対内部 Hom の標的の順序を交換する同型。
方針：順方向と逆方向の同じ比較構成を、二度の交換の恒等式でまとめる。
規約：対象の充填性や二つの始域の射の単射性は不要。
使われ方：境界を固定する関手 V′ の相対余錐条件への移送。 -/
def kanRelativeHomInterchangeIso (si : internalHom.PullbackObjObj i p)
    (sj : internalHom.PullbackObjObj j p) (s : internalHom.PullbackObjObj j si.π)
    (t : internalHom.PullbackObjObj i sj.π) : s.pt ≅ t.pt where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeHomInterchangeMap si sj s t
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeHomInterchangeMap sj si t s
  hom_inv_id := kanRelativeHomInterchangeMap_comp si sj s t
  inv_hom_id := kanRelativeHomInterchangeMap_comp sj si t s

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
