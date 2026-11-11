module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.BousfieldKanReindex
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanColimit
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedColimit

/-!
概要：各 Over 圏上の Bousfield–Kan coend を元の添字上の図式に束ねる。
方針：Over.map に沿う標準添字変更を構造射に使う。
規約：各 coend の添字は変わるが、元の係数の左端は保つ。
使われ方：filtered な Bousfield–Kan augmentation の各段による表示。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

variable {I : Type u} [SmallCategory I]

/-- 概要：Over の底の射に沿う各段の coend の構造射。
方針：Over.map に沿って Bousfield–Kan coend の添字を変更する。
規約：係数の忘却関手との合成は元の係数と厳密に同じ。使われ方：図式の構造射。 -/
def overBousfieldKanMap (F : I ⥤ SSet.{u}) {i j : I} (f : i ⟶ j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanColimit (Over.forget i ⋙ F) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanColimit (Over.forget j ⋙ F) :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanReindex (Over.forget j ⋙ F) (Over.map f)

/-- 概要：Over の恒等による構造射は恒等射。
方針：Over.map の恒等則と添字変更の単位則を使う。
規約：元の各段を保持する。使われ方：図式の恒等則。 -/
lemma overBousfieldKanMap_id (F : I ⥤ SSet.{u}) (i : I) :
    overBousfieldKanMap F (𝟙 i) = 𝟙 _ := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanReindex_congr (Over.forget i ⋙ F) (Over.mapId_eq i)
  change (𝟙 _) ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanReindex (Over.forget i ⋙ F) (𝟭 (Over i)) =
    overBousfieldKanMap F (𝟙 i) at h
  rw [Category.id_comp, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanReindex_id] at h
  exact h.symm

/-- 概要：Over の二段の構造射は元の射の合成による構造射。
方針：Over.map の合成則と添字変更の合成則を使う。
規約：実際の coend の射の等式。使われ方：図式の合成則。 -/
lemma overBousfieldKanMap_comp (F : I ⥤ SSet.{u}) {i j k : I} (f : i ⟶ j) (g : j ⟶ k) :
    overBousfieldKanMap F (f ≫ g) = overBousfieldKanMap F f ≫ overBousfieldKanMap F g := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanReindex_comp (Over.forget k ⋙ F) (Over.map g) (Over.map f)
  have hc := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanReindex_congr (Over.forget k ⋙ F) (Over.mapComp_eq f g)
  change (𝟙 _) ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanReindex (Over.forget k ⋙ F) (Over.map f ⋙ Over.map g) =
    overBousfieldKanMap F (f ≫ g) at hc
  rw [Category.id_comp] at hc
  exact hc.symm.trans h.symm

/-- 概要：各 Over 圏上の coend を束ねた元の添字の図式。
方針：標準添字変更の構造射とその単位・合成則を使う。
規約：filtered 性は定義には不要。使われ方：元の coend の filtered 表示。 -/
def overBousfieldKanDiagram (F : I ⥤ SSet.{u}) : I ⥤ SSet.{u} where
  obj i := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanColimit (Over.forget i ⋙ F)
  map f := overBousfieldKanMap F f
  map_id := overBousfieldKanMap_id F
  map_comp f g := overBousfieldKanMap_comp F f g

/-- 概要：Over の構造射の各普遍脚での公式。
方針：一般の添字変更の式を元の忘却図式で表示する。
規約：始域の依存する表示を正規化する。使われ方：augmentation の自然性。 -/
lemma overBousfieldKanι_map (F : I ⥤ SSet.{u}) {i j : I} (f : i ⟶ j) (a : Over i) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (Over i)ᵒᵖ) (Over.forget i ⋙ F) a ≫
      overBousfieldKanMap F f =
        (F.obj a.left ◁ nerveMap (Over.post (Over.map f).op (X := Opposite.op a))) ≫
          _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (Over j)ᵒᵖ) (Over.forget j ⋙ F)
            ((Over.map f).obj a) :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanι_reindex (Over.forget j ⋙ F) (Over.map f) a

end SerrePositivity.InfinityCategories.Project.FilteredExchange
