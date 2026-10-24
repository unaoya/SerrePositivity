module

public import SerrePositivity.InfinityCategories.Stable.CosliceRestriction

public import SerrePositivity.InfinityCategories.F1B.Cofinality.CofinalAnodyneRecognition
public import SerrePositivity.InfinityCategories.Core.ColimitDiagramIso

/-!
概要：任意の right cofinal な形状写像で、指定した native 余錐の余極限性を保存・反映する。
方針：right anodyne と trivial Kan の分解を使い、後因子は同値な単射切断で処理する。
規約：元の cofinal 写像に単射性を仮定しない。元の余錐の制限を返す。
使われ方：小さい κ-filtered 添字から cofinal poset 上の同じ余錐へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 図式の等号で移した余錐の全単体の値は、元の値を変えない。 -/
lemma sliceUnder_eqToIso_val {K X : SSet.{u}} {F G : K ⟶ X} (h : F = G)
    {n : SimplexCategoryᵒᵖ} (c : (sliceUnder F).obj n) :
    ((eqToIso (congrArg sliceUnder h)).hom.app n c).val = c.val := by
  cases h
  rfl

/-- trivial Kan な形状写像による、元の余錐全体の制限は同値。 -/
lemma sliceUnderRestrict_equivalence_of_trivialKan {Z K X : SSet.{u}}
    [Quasicategory K] [Quasicategory X] (p : Z ⟶ K) [TrivialKanFibration p] (F : K ⟶ X) :
    IsQCatEquivalence (sliceUnderRestrict F p) := by
  have : Quasicategory Z := quasicategory_of_innerFibration p
  obtain ⟨s, hs⟩ := trivialKanFibration_exists_section p
  have : Mono s := mono_of_mono_fac hs
  have hp := (qCatEquivalenceOfTrivialKanFibration p).isQCatEquivalence
  have hsp : IsQCatEquivalence (s ≫ p) := by
    rw [hs]
    exact (QCatEquivalence.refl K).isQCatEquivalence
  have hs' := hp.cancel_right hsp
  have : TrivialKanFibration (sliceUnderRestrict (p ≫ F) s) :=
    sliceUnderRestrict_trivialKanFibration_of_precompositionEquivalence
      (p ≫ F) s hs'.isPrecompositionEquivalence
  have hF : s ≫ (p ≫ F) = F := by rw [← Category.assoc, hs, Category.id_comp]
  let e := eqToIso (congrArg sliceUnder hF)
  let T := sliceUnderRestrict (p ≫ F) s ≫ e.hom
  have ht : IsQCatEquivalence T :=
    (qCatEquivalenceOfTrivialKanFibration (sliceUnderRestrict (p ≫ F) s)).isQCatEquivalence.comp
      (qCatEquivalenceOfIso e).isQCatEquivalence
  have hrt : sliceUnderRestrict F p ≫ T = 𝟙 _ := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro c
    apply Subtype.ext
    change ((eqToIso (congrArg sliceUnder hF)).hom.app n
      ((sliceUnderRestrict (p ≫ F) s).app n ((sliceUnderRestrict F p).app n c))).val = c.val
    rw [sliceUnder_eqToIso_val hF]
    change joinMap s (𝟙 _) ≫ (joinMap p (𝟙 _) ≫ c.val) = c.val
    rw [← Category.assoc, ← joinMap_comp, Category.id_comp, hs, joinMap_id, Category.id_comp]
  apply ht.cancel_right
  rw [hrt]
  exact (QCatEquivalence.refl _).isQCatEquivalence

/-- 任意の right cofinal map による、同じ全余錐圏の制限は同値。 -/
lemma sliceUnderRestrict_equivalence_of_rightCofinal {A K X : SSet.{u}}
    [Quasicategory K] [Quasicategory X] (f : A ⟶ K) (hf : IsRightCofinal f) (F : K ⟶ X) :
    IsQCatEquivalence (sliceUnderRestrict F f) := by
  obtain ⟨Z, j, p, hm, hj, hp, he⟩ := hf.exists_anodyne_trivialKan_factorization
  have : Mono j := hm
  have : TrivialKanFibration p := hp
  have : TrivialKanFibration (sliceUnderRestrict (p ≫ F) j) :=
    sliceUnderRestrict_trivialKanFibration (p ≫ F) j hj
  have hc := (sliceUnderRestrict_equivalence_of_trivialKan p F).comp
    (qCatEquivalenceOfTrivialKanFibration (sliceUnderRestrict (p ≫ F) j)).isQCatEquivalence
  change IsQCatEquivalence (sliceUnderRestrict F p ≫ sliceUnderRestrict (p ≫ F) j) at hc
  rw [sliceUnderRestrict_comp] at hc
  exact (congrArg (fun v : A ⟶ K => IsQCatEquivalence (sliceUnderRestrict F v)) he).mp hc

/-- 元の right cofinal な制限は、指定余錐の余極限性を保存し反映する。 -/
lemma isColimitCone_iff_restrict_rightCofinal {A K X : SSet.{u}}
    [Quasicategory K] [Quasicategory X] (f : A ⟶ K) (hf : IsRightCofinal f)
    {F : K ⟶ X} (c : JoinCocone F) : IsColimitCone c ↔ IsColimitCone (c.restrict f) :=
  (sliceUnderRestrict_equivalence_of_rightCofinal f hf F).choose.isInitialVertex_iff c

end SerrePositivity.InfinityCategories.F2.Ind
