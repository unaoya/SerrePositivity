module

public import SerrePositivity.InfinityCategories.HomotopyLimits.NonemptyFiniteSSetProduct
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanTensorAdjunction
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ContinuousKanProductUnit
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanWeakFunctoriality
public import SerrePositivity.InfinityCategories.F1B.Homotopy.WeakWhitehead

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
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の有限非空 Kan 族の反復積は Kan。 -/
lemma nonemptyFiniteSSetProduct_kanComplex (n : ℕ) (E : Fin (n + 1) → SSet.{u})
    (hE : ∀ i, KanComplex (E i)) : KanComplex (nonemptyFiniteSSetProduct n E) := by
  induction n with
  | zero => exact hE 0
  | succ n ih =>
    have : KanComplex (E 0) := hE 0
    have : KanComplex (nonemptyFiniteSSetProduct n (fun i ↦ E i.succ)) :=
      ih _ (fun i ↦ hE i.succ)
    exact kanTensor_isKan _ _

/-- 元の Kan 単位の有限非空反復積は anodyne。 -/
lemma continuousKanFiniteProductUnit_anodyne (n : ℕ) (E : Fin (n + 1) → SSet.{u}) :
    anodyneExtensions (nonemptyFiniteSSetProductMap n
      (fun i ↦ F2.continuousKanReplacementUnit.app (E i))) := by
  induction n with
  | zero => exact F2.continuousKanReplacementUnit_anodyne _
  | succ n ih =>
    change anodyneExtensions (F2.continuousKanReplacementUnit.app (E 0) ⊗ₘ
      nonemptyFiniteSSetProductMap n (fun i ↦ F2.continuousKanReplacementUnit.app (E i.succ)))
    rw [tensorHom_def]
    exact anodyneExtensions.comp_mem _ _
      ((F2.continuousKanReplacementUnit_anodyne _).whiskerRight _)
      ((ih (fun i ↦ E i.succ)).whiskerLeft _)

/-- 元の有限非空積の Kan 置換から、元の各置換の反復積への比較。 -/
def continuousKanFiniteProductComparison : (n : ℕ) → (E : Fin (n + 1) → SSet.{u}) →
    (F2.continuousKanReplacement.obj (nonemptyFiniteSSetProduct n E) ⟶
      nonemptyFiniteSSetProduct n (fun i ↦ F2.continuousKanReplacement.obj (E i)))
  | 0, _ => 𝟙 _
  | n + 1, E => lift (F2.continuousKanReplacement.map
      (fst (E 0) (nonemptyFiniteSSetProduct n (fun i ↦ E i.succ))))
      (F2.continuousKanReplacement.map
        (snd (E 0) (nonemptyFiniteSSetProduct n (fun i ↦ E i.succ))) ≫
          continuousKanFiniteProductComparison n (fun i ↦ E i.succ))

/-- 元の比較の全射影は、元の射影の Kan 像。 -/
lemma continuousKanFiniteProductComparison_projection (n : ℕ)
    (E : Fin (n + 1) → SSet.{u}) (i : Fin (n + 1)) :
    continuousKanFiniteProductComparison n E ≫ nonemptyFiniteSSetProjection n
        (fun i ↦ F2.continuousKanReplacement.obj (E i)) i =
      F2.continuousKanReplacement.map (nonemptyFiniteSSetProjection n E i) := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp only [continuousKanFiniteProductComparison, nonemptyFiniteSSetProjection,
      nonemptyFiniteSSetProduct,
      eqToHom_refl, Category.id_comp, F2.continuousKanReplacement.map_id]
  | succ n ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact lift_fst _ _
    · change lift _ _ ≫ (_ ≫ _) = _
      rw [← Category.assoc, lift_snd, Category.assoc, ih, ← Functor.map_comp]
      rfl

/-- 元の比較と元の Kan 単位の全成分は厳密に可換。 -/
lemma continuousKanFiniteProductComparison_unit (n : ℕ) (E : Fin (n + 1) → SSet.{u}) :
    F2.continuousKanReplacementUnit.app (nonemptyFiniteSSetProduct n E) ≫
      continuousKanFiniteProductComparison n E =
        nonemptyFiniteSSetProductMap n (fun i ↦ F2.continuousKanReplacementUnit.app (E i)) := by
  induction n with
  | zero => exact Category.comp_id _
  | succ n ih =>
    change _ ≫ lift _ _ = _ ⊗ₘ _
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, tensorHom_fst,
        ← F2.continuousKanReplacementUnit.naturality, Functor.id_map]
    · rw [Category.assoc, lift_snd, tensorHom_snd, ← Category.assoc,
        ← F2.continuousKanReplacementUnit.naturality, Functor.id_map, Category.assoc, ih]

/-- 元の有限非空積の Kan 比較は弱ホモトピー同値。 -/
lemma continuousKanFiniteProductComparison_isWeakHomotopyEquivalence (n : ℕ)
    (E : Fin (n + 1) → SSet.{u}) :
    IsWeakHomotopyEquivalence (continuousKanFiniteProductComparison n E) := by
  apply (F2.continuousKanReplacementUnit_isWeakHomotopyEquivalence _).cancel_left
  rw [continuousKanFiniteProductComparison_unit]
  intro Z _
  exact (homotopyEquivalence_pre_of_anodyne _
    (continuousKanFiniteProductUnit_anodyne n E) Z).mapPiZero_bijective

/-- 元の比較は元の全有限非空積の間の実際のホモトピー逆を持つ。 -/
lemma continuousKanFiniteProductComparison_homotopyEquivalence (n : ℕ)
    (E : Fin (n + 1) → SSet.{u}) :
    IsSimplicialHomotopyEquivalence (continuousKanFiniteProductComparison n E) := by
  have : KanComplex (nonemptyFiniteSSetProduct n
      (fun i ↦ F2.continuousKanReplacement.obj (E i))) :=
    nonemptyFiniteSSetProduct_kanComplex _ _ (fun _ ↦ inferInstance)
  exact (continuousKanFiniteProductComparison_isWeakHomotopyEquivalence n E
    ).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.HomotopyLimits
