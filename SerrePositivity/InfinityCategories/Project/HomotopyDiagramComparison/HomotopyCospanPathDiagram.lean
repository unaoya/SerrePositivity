module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanHomotopyInvariance
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanWhiteheadComparison
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyPathReplacement
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan

/-!
概要：二枝のホモトピー可換な比較を、比較先の cospan の path 置換への厳密な自然変換にする。
方針：各枝のホモトピーを可逆 path の族にし、元の終端成分をそのまま保持する。
規約：構造射の fibration 性は不要。選んだホモトピー全体を入力する。
使われ方：余錐空間の制限と Hom の前合成の二つの正方形を end の比較へ束ねる。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {L M R L' M' R' : SSet.{u}}
  (f' : L' ⟶ M') (g' : R' ⟶ M')

/-- 両枝を path 置換し、共通終端を保った cospan。 -/
def cospanPathDiagram : AsSmall.{u} WalkingCospan ⥤ SSet.{u} :=
  AsSmall.down ⋙ cospan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap f') (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap g')

/-- 比較先の cospan は、各枝の定値 path により path 置換へ自然に写る。 -/
def cospanPathSection : (AsSmall.down ⋙ cospan f' g') ⟶ cospanPathDiagram f' g' where
  app i := by
    rcases i with ⟨i⟩
    cases i with
    | none => exact 𝟙 M'
    | some k =>
      cases k with
      | left => exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection f'
      | right => exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection g'
  naturality i j h := by
    rcases i with ⟨i⟩
    rcases j with ⟨j⟩
    rcases h with ⟨h⟩
    change WidePullbackShape.Hom i j at h
    cases h with
    | id i =>
      cases i with
      | none => rfl
      | some k => cases k <;> rfl
    | term k =>
      cases k with
      | left =>
        change f' ≫ 𝟙 M' = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection f' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap f'
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection_map, Category.comp_id]
      | right =>
        change g' ≫ 𝟙 M' = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection g' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap g'
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection_map, Category.comp_id]

variable [KanComplex M'] (f : L ⟶ M) (g : R ⟶ M)
  (a : L ⟶ L') (b : M ⟶ M') (c : R ⟶ R')
  (Hf : SSet.Homotopy (f ≫ b) (a ≫ f')) (Hg : SSet.Homotopy (g ≫ b) (c ≫ g'))

/-- 二つの指定ホモトピーは、path 置換した比較先への厳密な自然変換を与える。 -/
def homotopyCospanMap : (AsSmall.down ⋙ cospan f g) ⟶ cospanPathDiagram f' g' where
  app i := by
    rcases i with ⟨i⟩
    cases i with
    | none => exact b
    | some k =>
      cases k with
      | left =>
        exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.homotopyPathReplacementLift f' a
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.simplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy Hf).symm)
      | right =>
        exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.homotopyPathReplacementLift g' c
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.simplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy Hg).symm)
  naturality i j h := by
    rcases i with ⟨i⟩
    rcases j with ⟨j⟩
    rcases h with ⟨h⟩
    change WidePullbackShape.Hom i j at h
    cases h with
    | id i =>
      cases i with
      | none => rfl
      | some k => cases k <;> rfl
    | term k =>
      cases k with
      | left =>
        change f ≫ b = _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.homotopyPathReplacementLift f' a _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap f'
        rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.homotopyPathReplacementLift_map]
      | right =>
        change g ≫ b = _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.homotopyPathReplacementLift g' c _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap g'
        rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.homotopyPathReplacementLift_map]

/-- 左成分の path 置換への比較は、元の左成分を射影で厳密に回収する。 -/
lemma homotopyCospanMap_left_projection :
    (homotopyCospanMap f' g' f g a b c Hf Hg).app (AsSmall.up.obj WalkingCospan.left) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection f' = a :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.homotopyPathReplacementLift_projection _ _ _

/-- 右成分の path 置換への比較は、元の右成分を射影で厳密に回収する。 -/
lemma homotopyCospanMap_right_projection :
    (homotopyCospanMap f' g' f g a b c Hf Hg).app (AsSmall.up.obj WalkingCospan.right) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection g' = c :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.homotopyPathReplacementLift_projection _ _ _

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
