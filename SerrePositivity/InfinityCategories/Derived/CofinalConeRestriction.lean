module
public import SerrePositivity.InfinityCategories.F1B.Cofinality.LimitExistence
public import SerrePositivity.InfinityCategories.Derived.RoofSliceTransport
/-!
概要：left cofinal な任意の実写像による錐圏の制限が ∞ 圏の同値であることを証明する。
方針：trivial Kan 後因子を同値な単射切断で処理し、left anodyne 前因子の制限と合成する。
規約：元の cofinal 写像の単射性を仮定しない。使われ方：指定右 Kan 錐の極限性の反映。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
/-- trivial Kan な形状写像による錐制限は、任意 quasicategory 値図式で同値。 -/
lemma sliceOverRestrict_isQCatEquivalence_of_trivialKanFibration {Z B X : SSet.{u}}
    [Quasicategory B] [Quasicategory X] (p : Z ⟶ B) [TrivialKanFibration p] (F : B ⟶ X) :
    IsQCatEquivalence (sliceOverRestrict F p) := by
  have : Quasicategory Z := quasicategory_of_innerFibration p
  obtain ⟨s, hs⟩ := trivialKanFibration_exists_section p
  have : Mono s := mono_of_mono_fac hs
  have hp := (qCatEquivalenceOfTrivialKanFibration p).isQCatEquivalence
  have hsp : IsQCatEquivalence (s ≫ p) := by
    rw [hs]
    exact (qCatEquivalenceOfIso (Iso.refl B)).isQCatEquivalence
  have hs' := hp.cancel_right hsp
  have : TrivialKanFibration (sliceOverRestrict (p ≫ F) s) :=
    sliceOverRestrict_trivialKanFibration_of_precompositionEquivalence
      (p ≫ F) s hs'.isPrecompositionEquivalence
  have hF : s ≫ (p ≫ F) = F :=
    (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q ≫ F) hs).trans (Category.id_comp _))
  let e := eqToIso (congrArg sliceOver hF)
  let T := sliceOverRestrict (p ≫ F) s ≫ e.hom
  have ht : IsQCatEquivalence T :=
    (qCatEquivalenceOfTrivialKanFibration (sliceOverRestrict (p ≫ F) s)).isQCatEquivalence.comp
      (qCatEquivalenceOfIso e).isQCatEquivalence
  have hrt : sliceOverRestrict F p ≫ T = 𝟙 _ := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro c
    apply Subtype.ext
    change ((eqToIso (congrArg sliceOver hF)).hom.app n
      ((sliceOverRestrict (p ≫ F) s).app n ((sliceOverRestrict F p).app n c))).val = c.val
    rw [roofSliceTransport_val hF]
    change joinMap (𝟙 _) s ≫ (joinMap (𝟙 _) p ≫ c.val) = c.val
    rw [← Category.assoc, ← joinMap_comp, Category.id_comp, hs, joinMap_id, Category.id_comp]
  apply ht.cancel_right
  rw [hrt]
  exact (QCatEquivalence.refl _).isQCatEquivalence
/-- 任意 left cofinal な形状写像に沿う錐圏の制限は、実際の ∞ 圏の同値。 -/
lemma sliceOverRestrict_isQCatEquivalence_of_leftCofinal {A B X : SSet.{u}}
    [Quasicategory B] [Quasicategory X] (u : A ⟶ B) (hu : IsLeftCofinal u) (F : B ⟶ X) :
    IsQCatEquivalence (sliceOverRestrict F u) := by
  obtain ⟨Z, j, p, hm, hj, hp, he⟩ := hu.exists_anodyne_trivialKan_factorization
  have : Mono j := hm
  have : TrivialKanFibration p := hp
  have : TrivialKanFibration (sliceOverRestrict (p ≫ F) j) :=
    sliceOverRestrict_trivialKanFibration (p ≫ F) j hj
  have hc := (sliceOverRestrict_isQCatEquivalence_of_trivialKanFibration p F).comp
    (qCatEquivalenceOfTrivialKanFibration (sliceOverRestrict (p ≫ F) j)).isQCatEquivalence
  change IsQCatEquivalence (sliceOverRestrict F p ≫ sliceOverRestrict (p ≫ F) j) at hc
  rw [← sliceOverRestrict_comp] at hc
  exact (congrArg (fun v : A ⟶ B => IsQCatEquivalence (sliceOverRestrict F v)) he).mp hc
end SerrePositivity.InfinityCategories
