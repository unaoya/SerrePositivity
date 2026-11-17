module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFunctorialFrames
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.ModelRelative
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.WeakNerveInverts
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LocalizationSourceIso

/-!
概要：元のstrict図式の局所化を、同じモデル圏のAsSmall表示からも使う。
方針：対象・射の宇宙の包みの順逆をnerveで照合し、同じ弱辺の実像で局所化を移す。
規約：値域と指定局所化射は変えない。
使われ方：HTT 4.2.4.4の写像空間比較で、実frameと元の局所化を接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local instance isw1StrictDiagramModelLocalizationLocal1 : _root_.HomotopicalAlgebra.ModelCategory (StrictComplexDiagram A d) :=
  strictDiagramReedyModelCategory A d

/-- 元の全図式を同じAsSmall表示へ包む通常関手。 -/
def strictDiagramModelUp : StrictComplexDiagram A d ⥤
    (modelRelativeCategory (StrictComplexDiagram A d)).category := AsSmall.up

/-- 同じAsSmall表示の元の全図式への通常関手。 -/
def strictDiagramModelDown : (modelRelativeCategory (StrictComplexDiagram A d)).category ⥤
    StrictComplexDiagram A d := AsSmall.down

/-- 対象と射をAsSmallで包んでも、元の全nerveと同じ実同型を持つ。 -/
def strictDiagramModelNerveIso :
    strictComplexDiagramNerve A d ≅
      nerve (modelRelativeCategory (StrictComplexDiagram A d)).category where
  hom :=
    { app n := ↾fun F => F ⋙ strictDiagramModelUp A d
      naturality := by
        intro n m α
        apply ConcreteCategory.hom_ext
        intro F
        rfl }
  inv :=
    { app n := ↾fun F => F ⋙ strictDiagramModelDown A d
      naturality := by
        intro n m α
        apply ConcreteCategory.hom_ext
        intro F
        rfl }
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro F
    apply CategoryTheory.Functor.hext
    · intro i
      rfl
    · intro i j f
      rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro F
    apply CategoryTheory.Functor.hext
    · intro i
      rfl
    · intro i j f
      rfl

/-- 同じ宇宙表示の順射は、元のobjectwise擬同型辺を正確に同じモデル弱辺へ送る。 -/
lemma strictDiagramModelNerveIso_weakEdges :
    (strictDiagramModelNerveIso A d).hom.app (Opposite.op ⦋1⦌) '' strictDiagramWeakEdges A d =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (modelRelativeCategory (StrictComplexDiagram A d)) := by
  ext s
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨X, Y, f, rfl⟩ := ComposableArrows.mk₁_surjective t
    refine ⟨(strictDiagramModelUp A d).obj X, (strictDiagramModelUp A d).obj Y,
      (strictDiagramModelUp A d).map f, ?_, ?_⟩
    · change _root_.HomotopicalAlgebra.weakEquivalences (StrictComplexDiagram A d) f
      change (strictDiagramReedyModelCategory A d).categoryWithWeakEquivalences.weakEquivalences f
      rw [strictDiagramReedyModelCategory_weakEquivalences]
      exact ht
    · change ComposableArrows.mk₁ f ⋙ strictDiagramModelUp A d = _
      exact ComposableArrows.ext₁
        (F := ComposableArrows.mk₁ f ⋙ strictDiagramModelUp A d)
        (G := ComposableArrows.mk₁ ((strictDiagramModelUp A d).map f))
        rfl rfl (by simp)
  · rintro ⟨X, Y, f, hf, rfl⟩
    refine ⟨ComposableArrows.mk₁ ((strictDiagramModelDown A d).map f), ?_, ?_⟩
    · change strictDiagramQuasiIsos A d ((strictDiagramModelDown A d).map f)
      change (strictDiagramReedyModelCategory A d).categoryWithWeakEquivalences.weakEquivalences _ at hf
      rw [strictDiagramReedyModelCategory_weakEquivalences] at hf
      exact hf
    · change ComposableArrows.mk₁ ((strictDiagramModelDown A d).map f) ⋙
        strictDiagramModelUp A d = _
      exact ComposableArrows.ext₁
        (F := ComposableArrows.mk₁ ((strictDiagramModelDown A d).map f) ⋙
          strictDiagramModelUp A d) (G := ComposableArrows.mk₁ f)
        rfl rfl (by
          simp only [eqToHom_refl, Category.id_comp, Category.comp_id,
            CategoryTheory.Functor.comp_map]
          change ULift.up f.down = f
          exact ULift.ext rfl)

/-- 同じ指定局所化を、実モデル圏の元のAsSmall表示から読む。 -/
def strictDiagramModelLocalization :
    nerve (modelRelativeCategory (StrictComplexDiagram A d)).category ⟶
      StrictDiagramInfinity A d :=
  (strictDiagramModelNerveIso A d).inv ≫ strictDiagramLocalization A d

/-- 同じ弱辺の宇宙表示の移送は、元の∞局所化の普遍性を保つ。 -/
lemma strictDiagramModelLocalization_isLocalization :
    IsLocalization (strictDiagramModelLocalization A d)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (modelRelativeCategory (StrictComplexDiagram A d))) := by
  apply isLocalization_of_precomposeIso (strictDiagramModelNerveIso A d)
    (strictDiagramModelLocalization A d) (strictDiagramWeakEdges A d) _
    (strictDiagramModelNerveIso_weakEdges A d)
  simpa only [strictDiagramModelLocalization, Iso.hom_inv_id_assoc] using
    strictDiagramLocalization_isLocalization A d

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
