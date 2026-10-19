module

public import SerrePositivity.InfinityCategories.HomotopyLimits.HomotopyCospanPathDiagram

/-!
概要：成分ごとに同値な二つのホモトピー可換な cospan の Bousfield–Kan end を比較する。
方針：比較先の path 置換への二本の厳密な自然変換に、既存の end の同値不変性を適用する。
規約：図式の構造射には fibration 性を要求せず、成分の Kan 性と実際のホモトピーを使う。
使われ方：部分余極限の Hom の二枝と、元の余錐空間の極限との比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 三つの Kan 複体からなる小さい cospan は成分ごとに Kan。 -/
instance resizedCospan_obj_kanComplex {L M R : SSet.{u}}
    [KanComplex L] [KanComplex M] [KanComplex R] (f : L ⟶ M) (g : R ⟶ M)
    (i : AsSmall.{u} WalkingCospan) : KanComplex ((AsSmall.down ⋙ cospan f g).obj i) := by
  rcases i with ⟨i⟩
  cases i with
  | none => exact inferInstanceAs (KanComplex M)
  | some k =>
    cases k with
    | left => exact inferInstanceAs (KanComplex L)
    | right => exact inferInstanceAs (KanComplex R)

/-- Kan cospan の両枝の path 置換も成分ごとに Kan。 -/
instance cospanPathDiagram_obj_kanComplex {L M R : SSet.{u}}
    [KanComplex L] [KanComplex M] [KanComplex R] (f : L ⟶ M) (g : R ⟶ M)
    (i : AsSmall.{u} WalkingCospan) : KanComplex ((cospanPathDiagram f g).obj i) := by
  rcases i with ⟨i⟩
  cases i with
  | none => exact inferInstanceAs (KanComplex M)
  | some k =>
    cases k with
    | left => exact inferInstanceAs (KanComplex (equivalencePathReplacement f))
    | right => exact inferInstanceAs (KanComplex (equivalencePathReplacement g))

/-- Kan 複体の path 置換への定値 path の切断は単体的ホモトピー同値。 -/
lemma kanPathReplacementSection_homotopyEquivalence {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] (f : X ⟶ Y) :
    IsSimplicialHomotopyEquivalence (equivalencePathReplacementSection f) := by
  have hp := isQCatEquivalence_of_trivialKanFibration (equivalencePathReplacementProjection f)
  have hs : IsQCatEquivalence (equivalencePathReplacementSection f) := by
    apply hp.cancel_right
    rw [equivalencePathReplacementSection_projection]
    exact (qCatEquivalenceOfIso (Iso.refl _)).isQCatEquivalence
  exact hs.isSimplicialHomotopyEquivalence

variable {L M R L' M' R' : SSet.{u}}
  [KanComplex L] [KanComplex M] [KanComplex R]
  [KanComplex L'] [KanComplex M'] [KanComplex R']
  (f' : L' ⟶ M') (g' : R' ⟶ M')

/-- 比較先から path 置換への自然な切断は、各成分で実際のホモトピー同値。 -/
lemma cospanPathSection_app_homotopyEquivalence (i : AsSmall.{u} WalkingCospan) :
    IsSimplicialHomotopyEquivalence ((cospanPathSection f' g').app i) := by
  rcases i with ⟨i⟩
  cases i with
  | none => exact homotopyEquivalence_of_isIso (𝟙 M')
  | some k =>
    cases k with
    | left => exact kanPathReplacementSection_homotopyEquivalence f'
    | right => exact kanPathReplacementSection_homotopyEquivalence g'

/-- 比較先の end から path 置換した end への実際の誘導射。 -/
def cospanPathSectionEnd :
    weightedSections (bousfieldKanWeight (AsSmall.{u} WalkingCospan))
        (AsSmall.down ⋙ cospan f' g') ⟶
      weightedSections (bousfieldKanWeight (AsSmall.{u} WalkingCospan)) (cospanPathDiagram f' g') :=
  weightedSectionsMap _ (cospanPathSection f' g')

/-- 比較先の end と path 置換した end は実際の誘導射でホモトピー同値。 -/
lemma cospanPathSectionEnd_homotopyEquivalence :
    IsSimplicialHomotopyEquivalence (cospanPathSectionEnd f' g') :=
  bousfieldKanMap_homotopyEquivalence _ (cospanPathSection_app_homotopyEquivalence f' g')

variable (f : L ⟶ M) (g : R ⟶ M) (a : L ⟶ L') (b : M ⟶ M') (c : R ⟶ R')
  (Hf : SSet.Homotopy (f ≫ b) (a ≫ f')) (Hg : SSet.Homotopy (g ≫ b) (c ≫ g'))

/-- 二つのホモトピーによる厳密化は、成分の同値性を保つ。 -/
lemma homotopyCospanMap_app_homotopyEquivalence
    (ha : IsSimplicialHomotopyEquivalence a) (hb : IsSimplicialHomotopyEquivalence b)
    (hc : IsSimplicialHomotopyEquivalence c) (i : AsSmall.{u} WalkingCospan) :
    IsSimplicialHomotopyEquivalence ((homotopyCospanMap f' g' f g a b c Hf Hg).app i) := by
  rcases i with ⟨i⟩
  cases i with
  | none => exact hb
  | some k =>
    cases k with
    | left =>
      have hp := isQCatEquivalence_of_trivialKanFibration (equivalencePathReplacementProjection f')
      have he : IsQCatEquivalence
          ((homotopyCospanMap f' g' f g a b c Hf Hg).app (AsSmall.up.obj WalkingCospan.left)) := by
        apply hp.cancel_right
        rw [homotopyCospanMap_left_projection]
        exact ha.isQCatEquivalence
      exact he.isSimplicialHomotopyEquivalence
    | right =>
      have hp := isQCatEquivalence_of_trivialKanFibration (equivalencePathReplacementProjection g')
      have he : IsQCatEquivalence
          ((homotopyCospanMap f' g' f g a b c Hf Hg).app (AsSmall.up.obj WalkingCospan.right)) := by
        apply hp.cancel_right
        rw [homotopyCospanMap_right_projection]
        exact hc.isQCatEquivalence
      exact he.isSimplicialHomotopyEquivalence

/-- 二つのホモトピーで可換な比較から、path 置換した比較先の end への実際の射を得る。 -/
def homotopyCospanMapEnd :
    weightedSections (bousfieldKanWeight (AsSmall.{u} WalkingCospan))
        (AsSmall.down ⋙ cospan f g) ⟶
      weightedSections (bousfieldKanWeight (AsSmall.{u} WalkingCospan)) (cospanPathDiagram f' g') :=
  weightedSectionsMap _ (homotopyCospanMap f' g' f g a b c Hf Hg)

/-- 成分ごとの同値とホモトピー可換性から、二つの cospan の end の共通の同値模型を得る。 -/
lemma homotopyCospanMapEnd_homotopyEquivalence
    (ha : IsSimplicialHomotopyEquivalence a) (hb : IsSimplicialHomotopyEquivalence b)
    (hc : IsSimplicialHomotopyEquivalence c) :
    IsSimplicialHomotopyEquivalence (homotopyCospanMapEnd f' g' f g a b c Hf Hg) :=
  bousfieldKanMap_homotopyEquivalence _
    (homotopyCospanMap_app_homotopyEquivalence f' g' f g a b c Hf Hg ha hb hc)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
