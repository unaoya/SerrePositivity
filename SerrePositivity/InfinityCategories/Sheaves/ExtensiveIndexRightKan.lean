module

public import SerrePositivity.InfinityCategories.Sheaves.ExtensiveLegRightCone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.EmptyShapeCone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RightKanLimitRestriction
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.NatTransHomotopyNaturality
public import Mathlib.AlgebraicTopology.SimplicialSet.Nonempty

/-!
概要：加えた終点の値が終対象なら、脚への制限に沿う元の指定右 Kan 条件が成り立つ。
方針：終点の局所 comma は空、脚の局所 comma は恒等三角形を初対象に持つ。
規約：HTT 4.3.2 の指定局所錐による判定。右 Kan 条件を追加仮定に置かない。
使われ方：S1 の有限被覆の指定全錐の極限性と積錐の極限性の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
namespace SerrePositivity.InfinityCategories.Sheaves
variable (I : Type u) [SmallCategory I] {E : SSet.{u}} [Quasicategory E]

/-- 終点での元の通常の局所錐は、空形状の同じ頂点の錐。 -/
lemma extensiveStarRightCone_postcomp_isLimit (H : nerve (WithTerminal I) ⟶ E)
    (hH : IsTerminalVertex (H.app _ (nerveVertex (WithTerminal.star : WithTerminal I)))) :
    IsLimitCone ((nerveCone ((Functor.RightExtension.mk
      (L := (WithTerminal.incl : I ⥤ WithTerminal I))
      (𝟭 (WithTerminal I)) (𝟙 (WithTerminal.incl : I ⥤ WithTerminal I))).coneAt
        WithTerminal.star)).postcomp H) := by
  letI := extensiveTerminalComma_isEmpty I
  have he : IsInitial (nerve (StructuredArrow (WithTerminal.star : WithTerminal I)
      (WithTerminal.incl : I ⥤ WithTerminal I))) :=
    SSet.isInitialOfNotNonempty (fun ⟨a⟩ => isEmptyElim (nerveEquiv a))
  apply (isLimitCone_iff_terminal_of_initialShape he _).mpr
  change IsTerminalVertex ((mapJoinCone H (nerveCone _)).vertex)
  rw [mapJoinCone_vertex, nerveCone_vertex]
  exact hH

/-- 元の通常の恒等余単位を係数へ送った指定円柱。 -/
abbrev extensiveIndexRightKanCounit (H : nerve (WithTerminal I) ⟶ E) :=
  kanRightCounitPostcomp (δ := nerveMap (WithTerminal.incl : I ⥤ WithTerminal I))
    (F := nerveMap (𝟭 (WithTerminal I)))
    (F₀ := nerveMap (WithTerminal.incl : I ⥤ WithTerminal I))
    (nerveNatTransHomotopy (𝟙 (WithTerminal.incl : I ⥤ WithTerminal I))) H

/-- 同じ円柱全体の射は、指定した制限の時間に定値な射。 -/
lemma extensiveIndexRightKanCounit_h (H : nerve (WithTerminal I) ⟶ E) :
    (extensiveIndexRightKanCounit I H).h =
      fst _ _ ≫ (nerveMap (WithTerminal.incl : I ⥤ WithTerminal I) ≫ H) := by
  change (nerveNatTransHomotopy (𝟙 (WithTerminal.incl : I ⥤ WithTerminal I))).h ≫ H = _
  simp only [nerveNatTransHomotopy_id, Category.assoc]

/-- 元の輸送の係数を簡約する前の同じ右 Kan 条件。 -/
lemma extensiveIndexRightKan_data (H : nerve (WithTerminal I) ⟶ E)
    (hH : IsTerminalVertex (H.app _ (nerveVertex (WithTerminal.star : WithTerminal I)))) :
    IsRightKanExtension (nerveMap (WithTerminal.incl : I ⥤ WithTerminal I))
      (nerveMap (WithTerminal.incl : I ⥤ WithTerminal I) ≫ H)
      (nerveMap (𝟭 (WithTerminal I)) ≫ H) (extensiveIndexRightKanCounit I H) := by
  intro v
  obtain ⟨a, rfl⟩ := (nerveEquiv (C := WithTerminal I)).symm.surjective v
  refine ⟨nerveRightConeTransportPostcomp (WithTerminal.incl : I ⥤ WithTerminal I)
    (F := 𝟭 (WithTerminal I)) (𝟙 (WithTerminal.incl : I ⥤ WithTerminal I)) a H, ?_⟩
  apply (nerveRightConeTransportPostcomp_isLimit_iff
    (WithTerminal.incl : I ⥤ WithTerminal I) (𝟙 _) a H).mpr
  cases a with
  | star => exact extensiveStarRightCone_postcomp_isLimit I H hH
  | of i => exact extensiveLegRightCone_postcomp_isLimit I H i

private lemma rightKan_refl_of_counit {A B X : SSet.{u}} [Quasicategory X]
    {δ : A ⟶ B} {p q : B ⟶ X} (hp : p = q)
    (α : SSet.Homotopy (δ ≫ p) (δ ≫ q)) (hα : α.h = fst _ _ ≫ (δ ≫ q))
    (hk : IsRightKanExtension δ (δ ≫ q) p α) :
    IsRightKanExtension δ (δ ≫ q) q
      (SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm (δ ≫ q))) := by
  cases hp
  have ha : α = SSet.RelativeMorphism.Homotopy.refl
      (SSet.RelativeMorphism.botEquiv.symm (δ ≫ p)) := by
    apply SSet.RelativeMorphism.Homotopy.ext
    exact hα
  cases ha
  exact hk

/-- 終点の値の終対象性から、同じ恒等余単位で右 Kan 条件を実際に証明する。 -/
lemma extensiveIndex_isRightKanExtension (H : nerve (WithTerminal I) ⟶ E)
    (hH : IsTerminalVertex (H.app _ (nerveVertex (WithTerminal.star : WithTerminal I)))) :
    IsRightKanExtension (nerveMap (WithTerminal.incl : I ⥤ WithTerminal I))
      (nerveMap (WithTerminal.incl : I ⥤ WithTerminal I) ≫ H) H
      (SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm
        (nerveMap (WithTerminal.incl : I ⥤ WithTerminal I) ≫ H))) := by
  have hid : nerveMap (𝟭 (WithTerminal I)) = 𝟙 (nerve (WithTerminal I)) :=
    nerveFunctor.map_id (Cat.of (WithTerminal I))
  have hp : nerveMap (𝟭 (WithTerminal I)) ≫ H = H := by
    rw [hid, Category.id_comp]
  exact rightKan_refl_of_counit hp (extensiveIndexRightKanCounit I H)
    (extensiveIndexRightKanCounit_h I H) (extensiveIndexRightKan_data I H hH)

/-- 星の値が終対象なら、元の全錐は脚への同じ制限が極限であるときちょうど極限。 -/
lemma extensiveIndex_restrict_isLimit_iff (H : nerve (WithTerminal I) ⟶ E)
    (hH : IsTerminalVertex (H.app _ (nerveVertex (WithTerminal.star : WithTerminal I))))
    (c : JoinCone H) :
    IsLimitCone c ↔ IsLimitCone
      (restrictJoinCone c (nerveMap (WithTerminal.incl : I ⥤ WithTerminal I))) :=
  isLimitCone_iff_restrict_of_rightKan_refl _ H (extensiveIndex_isRightKanExtension I H hH) c

end SerrePositivity.InfinityCategories.Sheaves
