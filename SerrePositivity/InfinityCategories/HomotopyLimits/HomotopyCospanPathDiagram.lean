module

public import SerrePositivity.InfinityCategories.HomotopyLimits.BousfieldKanHomotopyInvariance
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanWhiteheadComparison
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyPathReplacement
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
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {L M R L' M' R' : SSet.{u}}
  (f' : L' ⟶ M') (g' : R' ⟶ M')

/-- 両枝を path 置換し、共通終端を保った cospan。 -/
def cospanPathDiagram : AsSmall.{u} WalkingCospan ⥤ SSet.{u} :=
  AsSmall.down ⋙ cospan (equivalencePathReplacementMap f') (equivalencePathReplacementMap g')

/-- 比較先の cospan は、各枝の定値 path により path 置換へ自然に写る。 -/
def cospanPathSection : (AsSmall.down ⋙ cospan f' g') ⟶ cospanPathDiagram f' g' where
  app i := by
    rcases i with ⟨i⟩
    cases i with
    | none => exact 𝟙 M'
    | some k =>
      cases k with
      | left => exact equivalencePathReplacementSection f'
      | right => exact equivalencePathReplacementSection g'
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
        change f' ≫ 𝟙 M' = equivalencePathReplacementSection f' ≫ equivalencePathReplacementMap f'
        rw [equivalencePathReplacementSection_map, Category.comp_id]
      | right =>
        change g' ≫ 𝟙 M' = equivalencePathReplacementSection g' ≫ equivalencePathReplacementMap g'
        rw [equivalencePathReplacementSection_map, Category.comp_id]

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
        exact homotopyPathReplacementLift f' a
          (FunctorIso.simplicialHomotopy (functorIsoOfSimplicialHomotopy Hf).symm)
      | right =>
        exact homotopyPathReplacementLift g' c
          (FunctorIso.simplicialHomotopy (functorIsoOfSimplicialHomotopy Hg).symm)
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
        change f ≫ b = homotopyPathReplacementLift f' a _ ≫ equivalencePathReplacementMap f'
        rw [homotopyPathReplacementLift_map]
      | right =>
        change g ≫ b = homotopyPathReplacementLift g' c _ ≫ equivalencePathReplacementMap g'
        rw [homotopyPathReplacementLift_map]

/-- 左成分の path 置換への比較は、元の左成分を射影で厳密に回収する。 -/
lemma homotopyCospanMap_left_projection :
    (homotopyCospanMap f' g' f g a b c Hf Hg).app (AsSmall.up.obj WalkingCospan.left) ≫
      equivalencePathReplacementProjection f' = a :=
  homotopyPathReplacementLift_projection _ _ _

/-- 右成分の path 置換への比較は、元の右成分を射影で厳密に回収する。 -/
lemma homotopyCospanMap_right_projection :
    (homotopyCospanMap f' g' f g a b c Hf Hg).app (AsSmall.up.obj WalkingCospan.right) ≫
      equivalencePathReplacementProjection g' = c :=
  homotopyPathReplacementLift_projection _ _ _

end
end SerrePositivity.InfinityCategories.HomotopyLimits
