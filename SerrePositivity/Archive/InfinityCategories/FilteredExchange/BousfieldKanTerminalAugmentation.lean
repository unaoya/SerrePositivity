module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.BousfieldKanTerminalContraction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor

/-!
概要：終対象を持つ添字では通常の colimit への標準 Bousfield–Kan augmentation は弱同値。
方針：終対象の値との colimit の同型を介して、構成した収縮へ帰着する。
規約：元の図式の Kan 性は不要。
使われ方：filtered 比較の over 圏ごとの弱同値性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {I : Type u} [SmallCategory I] {t : I}

/-- 概要：終対象の値を頂点とする余錐は通常の余極限。
方針：任意の余錐の終対象での脚を普遍射に使う。
規約：元の脚を厳密に保つ。使われ方：選ばれた colimit と終対象の値の比較。 -/
def terminalIndexCocone_isColimit (F : I ⥤ SSet.{u}) (ht : IsTerminal t) :
    IsColimit (terminalIndexCocone F ht) where
  desc s := s.ι.app t
  fac s i := s.w (ht.from i)
  uniq s m hm := by
    have h := hm t
    change F.map (ht.from t) ≫ m = s.ι.app t at h
    simpa only [ht.hom_ext (ht.from t) (𝟙 t), F.map_id, Category.id_comp] using h

/-- 概要：選ばれた通常の colimit と終対象の値の標準同型。
方針：二つの実際の余極限余錐の一意性を使う。
規約：同型の向きは colimit から終対象の値。使われ方：augmentation の比較。 -/
def terminalIndexColimitIso (F : I ⥤ SSet.{u}) (ht : IsTerminal t) :
    colimit F ≅ F.obj t :=
  (colimit.isColimit F).coconePointUniqueUpToIso (terminalIndexCocone_isColimit F ht)

/-- 概要：標準 augmentation と終対象の値への比較の合成は直接の augmentation。
方針：全ての重み付き脚で余極限の同型の脚の式を使う。
規約：元の標準比較射の等式。使われ方：弱同値性の右因子の消去。 -/
lemma bousfieldKanAugmentation_terminal_factor (F : I ⥤ SSet.{u}) (ht : IsTerminal t) :
    bousfieldKanAugmentation F ≫ (terminalIndexColimitIso F ht).hom =
      terminalBousfieldKanAugmentation F ht := by
  apply weightedColimit_hom_ext
  intro i
  rw [reassoc_of% bousfieldKanι_augmentation, terminalBousfieldKanAugmentation,
    weightedColimitι_augmentation]
  change _ ≫ colimit.ι F i ≫ (terminalIndexColimitIso F ht).hom =
    _ ≫ F.map (ht.from i)
  have h : colimit.ι F i ≫ (terminalIndexColimitIso F ht).hom = F.map (ht.from i) :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit F)
      (terminalIndexCocone_isColimit F ht) i
  exact congrArg (fun q ↦ fst (F.obj i)
    ((bousfieldKanWeight Iᵒᵖ).obj (Opposite.op i)) ≫ q) h

/-- 概要：終対象を持つ添字では通常の colimit への標準比較は弱同値。
方針：終対象の値への収縮と、通常の colimit の標準同型を用いる。
規約：図式の Kan 性を仮定しない。使われ方：filtered 比較の終対象を持つ段。 -/
lemma bousfieldKanAugmentation_isWeakHomotopyEquivalence_of_terminal
    (F : I ⥤ SSet.{u}) (ht : IsTerminal t) :
    IsWeakHomotopyEquivalence (bousfieldKanAugmentation F) := by
  let e := terminalIndexColimitIso F ht
  have he := (isPrecompositionEquivalence_of_iso e).isWeakHomotopyEquivalence
  apply he.cancel_right
  rw [bousfieldKanAugmentation_terminal_factor]
  exact terminalBousfieldKanAugmentation_isWeakHomotopyEquivalence F ht

end SerrePositivity.InfinityCategories.F2
