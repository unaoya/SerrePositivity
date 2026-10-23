module

public import SerrePositivity.InfinityCategories.F1.Simplicial.ReplacementEndCornerInner

/-!
概要：前合成同値の右持ち上げを持つ同値の、全境界持ち上げ。
方針：可逆 path 置換の標準切断を持ち上げ、元の射の厳密な切断を構成する。
規約：モデル構造の instance を仮定せず、充満忠実性と頂点全射性で判定する。
使われ方：比較四角形の終点側の比較を trivial Kan fibration に強める。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 前合成同値を右に持ち上げる同値には、厳密な切断が存在する。 -/
lemma IsQCatEquivalence.exists_section_of_kanEquivalenceLifting {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {p : X ⟶ Y} (hp : IsQCatEquivalence p)
    (hl : F1B.KanEquivalenceLifting p) : ∃ s : Y ⟶ X, s ≫ p = 𝟙 Y := by
  let j := equivalencePathReplacementSection p
  have hj : j ≫ equivalencePathReplacementProjection p = 𝟙 X :=
    equivalencePathReplacementSection_projection p
  have : Mono j := by
    constructor
    intro Z a b hab
    have he := congrArg (fun f ↦ f ≫ equivalencePathReplacementProjection p) hab
    simpa only [Category.assoc, hj, Category.comp_id] using he
  have he : IsQCatEquivalence j := by
    apply (isQCatEquivalence_of_trivialKanFibration
      (equivalencePathReplacementProjection p)).cancel_right
    rw [hj]
    exact (qCatEquivalenceOfIso (Iso.refl X)).isQCatEquivalence
  have := hl j inferInstance he.isPrecompositionEquivalence
  have sq : CommSq (𝟙 X) j p (equivalencePathReplacementMap p) := by
    constructor
    simpa only [Category.id_comp] using (equivalencePathReplacementSection_map p).symm
  have : TrivialKanFibration (equivalencePathReplacementMap p) :=
    hp.equivalencePathReplacementMap_trivialKanFibration
  obtain ⟨s, hs⟩ := trivialKanFibration_exists_section (equivalencePathReplacementMap p)
  exact ⟨s ≫ sq.lift, by rw [Category.assoc, sq.fac_right, hs]⟩

/-- 前合成同値を右に持ち上げる同値は、全ての境界を持ち上げる。 -/
lemma IsQCatEquivalence.trivialKanFibration_of_kanEquivalenceLifting {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {p : X ⟶ Y} (hp : IsQCatEquivalence p)
    (hl : F1B.KanEquivalenceLifting p) : TrivialKanFibration p := by
  have := hl.innerFibration
  obtain ⟨s, hs⟩ := hp.exists_section_of_kanEquivalenceLifting hl
  apply hp.isFullyFaithful.trivialKanFibration_of_surjective
  intro y
  refine ⟨s.app (Opposite.op ⦋0⦌) y, ?_⟩
  exact congrArg (fun f : Y ⟶ Y ↦ f.app (Opposite.op ⦋0⦌) y) hs

/-- 同値な横射と前合成同値を持ち上げる縦射の、終点比較は全境界を持ち上げる。 -/
lemma trivialKanFibration_replacementSquareEndCorner {A B X Y : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory X] [Quasicategory Y]
    (u : A ⟶ X) (v : B ⟶ Y) (p : A ⟶ B) (q : X ⟶ Y) (h : u ≫ q = p ≫ v)
    (hu : IsQCatEquivalence u) (hv : IsQCatEquivalence v)
    (hp : F1B.KanEquivalenceLifting p) (hq : F1B.KanEquivalenceLifting q) :
    TrivialKanFibration (replacementSquareEndCorner u v p q h) := by
  have ht := hv.equivalencePathReplacementMap_trivialKanFibration
  have : TrivialKanFibration (pullback.fst q (equivalencePathReplacementMap v)) :=
    ⟨trivialKanFibrations.pullback_fst _ _ ht.mem⟩
  have : Quasicategory (pullback q (equivalencePathReplacementMap v)) :=
    quasicategory_of_innerFibration (pullback.fst q (equivalencePathReplacementMap v))
  have he := replacementSquareEndCorner_isQCatEquivalence u v p q h hu hv
  exact he.trivialKanFibration_of_kanEquivalenceLifting
    (kanEquivalenceLifting_replacementSquareEndCorner u v p q h hp hq)

end SerrePositivity.InfinityCategories
