module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ContinuousKanWeakFunctoriality
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakWhitehead
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.KanTensorAdjunction
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.FiniteShapes.NonemptyFiniteSSetProduct

/-!
概要：元の有限非空積の Kan 置換から、元の各 Kan 置換の反復積への比較。
方針：元の二射影の Kan 像を反復し、元の単位の反復積の anodyne 性で同値性を証明する。
規約：元の全対象・比較射・置換単位を保持する。
使われ方：sifted 余極限と全有限積の交換における元の全空間の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の有限非空 Kan 族の反復積は Kan。 -/
lemma nonemptyFiniteSSetProduct_kanComplex (n : ℕ) (E : Fin (n + 1) → SSet.{u})
    (hE : ∀ i, KanComplex (E i)) : KanComplex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProduct n E) := by
  induction n with
  | zero => exact hE 0
  | succ n ih =>
    have : KanComplex (E 0) := hE 0
    have : KanComplex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProduct n (fun i ↦ E i.succ)) :=
      ih _ (fun i ↦ hE i.succ)
    exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensor_isKan _ _

/-- 元の Kan 単位の有限非空反復積は anodyne。 -/
lemma continuousKanFiniteProductUnit_anodyne (n : ℕ) (E : Fin (n + 1) → SSet.{u}) :
    anodyneExtensions (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProductMap n
      (fun i ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (E i))) := by
  induction n with
  | zero => exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit_anodyne _
  | succ n ih =>
    change anodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (E 0) ⊗ₘ
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProductMap n (fun i ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (E i.succ)))
    rw [tensorHom_def]
    exact anodyneExtensions.comp_mem _ _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit_anodyne _).whiskerRight _)
      ((ih (fun i ↦ E i.succ)).whiskerLeft _)

/-- 元の有限非空積の Kan 置換から、元の各置換の反復積への比較。 -/
def continuousKanFiniteProductComparison : (n : ℕ) → (E : Fin (n + 1) → SSet.{u}) →
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProduct n E) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProduct n (fun i ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (E i)))
  | 0, _ => 𝟙 _
  | n + 1, E => lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map
      (fst (E 0) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProduct n (fun i ↦ E i.succ))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map
        (snd (E 0) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProduct n (fun i ↦ E i.succ))) ≫
          continuousKanFiniteProductComparison n (fun i ↦ E i.succ))

/-- 元の比較の全射影は、元の射影の Kan 像。 -/
lemma continuousKanFiniteProductComparison_projection (n : ℕ)
    (E : Fin (n + 1) → SSet.{u}) (i : Fin (n + 1)) :
    continuousKanFiniteProductComparison n E ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProjection n
        (fun i ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (E i)) i =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProjection n E i) := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp only [continuousKanFiniteProductComparison, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProjection,
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProduct,
      eqToHom_refl, Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map_id]
  | succ n ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact lift_fst _ _
    · change lift _ _ ≫ (_ ≫ _) = _
      rw [← Category.assoc, lift_snd, Category.assoc, ih, ← Functor.map_comp]
      rfl

/-- 元の比較と元の Kan 単位の全成分は厳密に可換。 -/
lemma continuousKanFiniteProductComparison_unit (n : ℕ) (E : Fin (n + 1) → SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProduct n E) ≫
      continuousKanFiniteProductComparison n E =
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProductMap n (fun i ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (E i)) := by
  induction n with
  | zero => exact Category.comp_id _
  | succ n ih =>
    change _ ≫ lift _ _ = _ ⊗ₘ _
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, tensorHom_fst,
        ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality, Functor.id_map]
    · rw [Category.assoc, lift_snd, tensorHom_snd, ← Category.assoc,
        ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality, Functor.id_map, Category.assoc, ih]

/-- 元の有限非空積の Kan 比較は弱ホモトピー同値。 -/
lemma continuousKanFiniteProductComparison_isWeakHomotopyEquivalence (n : ℕ)
    (E : Fin (n + 1) → SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (continuousKanFiniteProductComparison n E) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.continuousKanReplacementUnit_isWeakHomotopyEquivalence _).cancel_left
  rw [continuousKanFiniteProductComparison_unit]
  intro Z _
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.homotopyEquivalence_pre_of_anodyne _
    (continuousKanFiniteProductUnit_anodyne n E) Z).mapPiZero_bijective

/-- 元の比較は元の全有限非空積の間の実際のホモトピー逆を持つ。 -/
lemma continuousKanFiniteProductComparison_homotopyEquivalence (n : ℕ)
    (E : Fin (n + 1) → SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (continuousKanFiniteProductComparison n E) := by
  have : KanComplex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProduct n
      (fun i ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (E i))) :=
    nonemptyFiniteSSetProduct_kanComplex _ _ (fun _ ↦ inferInstance)
  exact (continuousKanFiniteProductComparison_isWeakHomotopyEquivalence n E
    ).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
