module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.HomotopyCospanPathDiagram

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
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
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
    (i : AsSmall.{u} WalkingCospan) : KanComplex ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.cospanPathDiagram f g).obj i) := by
  rcases i with ⟨i⟩
  cases i with
  | none => exact inferInstanceAs (KanComplex M)
  | some k =>
    cases k with
    | left => exact inferInstanceAs (KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement f))
    | right => exact inferInstanceAs (KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement g))

/-- Kan 複体の path 置換への定値 path の切断は単体的ホモトピー同値。 -/
lemma kanPathReplacementSection_homotopyEquivalence {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection f) := by
  have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection f)
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection f) := by
    apply hp.cancel_right
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection_projection]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (Iso.refl _)).isQCatEquivalence
  exact hs.isSimplicialHomotopyEquivalence

variable {L M R L' M' R' : SSet.{u}}
  [KanComplex L] [KanComplex M] [KanComplex R]
  [KanComplex L'] [KanComplex M'] [KanComplex R']
  (f' : L' ⟶ M') (g' : R' ⟶ M')

/-- 比較先から path 置換への自然な切断は、各成分で実際のホモトピー同値。 -/
lemma cospanPathSection_app_homotopyEquivalence (i : AsSmall.{u} WalkingCospan) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.cospanPathSection f' g').app i) := by
  rcases i with ⟨i⟩
  cases i with
  | none => exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.homotopyEquivalence_of_isIso (𝟙 M')
  | some k =>
    cases k with
    | left => exact kanPathReplacementSection_homotopyEquivalence f'
    | right => exact kanPathReplacementSection_homotopyEquivalence g'

/-- 比較先の end から path 置換した end への実際の誘導射。 -/
def cospanPathSectionEnd :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan))
        (AsSmall.down ⋙ cospan f' g') ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan)) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.cospanPathDiagram f' g') :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap _ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.cospanPathSection f' g')

/-- 比較先の end と path 置換した end は実際の誘導射でホモトピー同値。 -/
lemma cospanPathSectionEnd_homotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (cospanPathSectionEnd f' g') :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanMap_homotopyEquivalence _ (cospanPathSection_app_homotopyEquivalence f' g')

variable (f : L ⟶ M) (g : R ⟶ M) (a : L ⟶ L') (b : M ⟶ M') (c : R ⟶ R')
  (Hf : SSet.Homotopy (f ≫ b) (a ≫ f')) (Hg : SSet.Homotopy (g ≫ b) (c ≫ g'))

/-- 二つのホモトピーによる厳密化は、成分の同値性を保つ。 -/
lemma homotopyCospanMap_app_homotopyEquivalence
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence a) (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence b)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence c) (i : AsSmall.{u} WalkingCospan) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyCospanMap f' g' f g a b c Hf Hg).app i) := by
  rcases i with ⟨i⟩
  cases i with
  | none => exact hb
  | some k =>
    cases k with
    | left =>
      have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection f')
      have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
          ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyCospanMap f' g' f g a b c Hf Hg).app (AsSmall.up.obj WalkingCospan.left)) := by
        apply hp.cancel_right
        rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyCospanMap_left_projection]
        exact ha.isQCatEquivalence
      exact he.isSimplicialHomotopyEquivalence
    | right =>
      have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection g')
      have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
          ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyCospanMap f' g' f g a b c Hf Hg).app (AsSmall.up.obj WalkingCospan.right)) := by
        apply hp.cancel_right
        rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyCospanMap_right_projection]
        exact hc.isQCatEquivalence
      exact he.isSimplicialHomotopyEquivalence

/-- 二つのホモトピーで可換な比較から、path 置換した比較先の end への実際の射を得る。 -/
def homotopyCospanMapEnd :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan))
        (AsSmall.down ⋙ cospan f g) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan)) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.cospanPathDiagram f' g') :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap _ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyCospanMap f' g' f g a b c Hf Hg)

/-- 成分ごとの同値とホモトピー可換性から、二つの cospan の end の共通の同値模型を得る。 -/
lemma homotopyCospanMapEnd_homotopyEquivalence
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence a) (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence b)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (homotopyCospanMapEnd f' g' f g a b c Hf Hg) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanMap_homotopyEquivalence _
    (homotopyCospanMap_app_homotopyEquivalence f' g' f g a b c Hf Hg ha hb hc)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
