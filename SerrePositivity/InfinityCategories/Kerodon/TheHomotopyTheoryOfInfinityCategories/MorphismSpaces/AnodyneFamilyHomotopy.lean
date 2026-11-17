module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.F1BKanComplexHomotopyClasses
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFamilyInvariance
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
# anodyne 局所化の全族の等式から実ホモトピーと全区間族の射を回収する

概要：Kan 標的への全写像の局所化内の等式を、同じ全パラメータの実ホモトピーへ反映する。
方針：Kan 標的の写像空間の全連結成分を反変関手として局所化の普遍性に通す。
規約：各点の π₀ だけで代用せず、始域の Kan 性を仮定しない。
使われ方：native roof の pinched 族と保存済み基準射の全区間三角形の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.SSet _root_.CategoryTheory.MonoidalClosed
open _root_.SerrePositivity.InfinityCategories _root_.SerrePositivity.SimplicialModel
open scoped _root_.Simplicial

lemma map_eq_of_anodyneQ_eq {D : Type v} [Category.{w} D] (L : SSet.{u} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) {A B : SSet.{u}} (f g : A ⟶ B)
    (h : AnodyneHomotopy.anodyneQ.map f = AnodyneHomotopy.anodyneQ.map g) :
    L.map f = L.map g := by
  let G := Localization.lift L hL AnodyneHomotopy.anodyneQ
  let e : AnodyneHomotopy.anodyneQ ⋙ G ≅ L := Localization.fac L hL _
  apply (cancel_epi (e.hom.app A)).1
  rw [← e.hom.naturality f, ← e.hom.naturality g]
  exact congrArg (fun k => k ≫ e.hom.app B) (congrArg G.map h)

lemma homotopy_of_anodyneQ_map_eq {A Z : SSet.{u}} [KanComplex Z] (f g : A ⟶ Z)
    (h : AnodyneHomotopy.anodyneQ.map f = AnodyneHomotopy.anodyneQ.map g) :
    Nonempty (SSet.Homotopy f g) := by
  have hL := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.map_eq_of_anodyneQ_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.homComponents Z).rightOp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.homComponents_inverts Z) f g h
  have hF : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.homComponents Z).map f.op =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.homComponents Z).map g.op := congrArg Quiver.Hom.unop hL
  have hπ := ConcreteCategory.congr_hom hF (SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 Z)))
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy f g).mp
  change SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f ≫ 𝟙 Z)) =
    SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (g ≫ 𝟙 Z)) at hπ
  simpa only [Category.comp_id] using hπ

lemma pinchedFamily_intervalHom_eq_of_anodyneQ_eq {K E : SSet.{u}} [Quasicategory E]
    {x y : E _⦋0⦌} (f g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y)
    (h : AnodyneHomotopy.anodyneQ.map f = AnodyneHomotopy.anodyneQ.map g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x y) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x y) := by
  obtain ⟨H⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homotopy_of_anodyneQ_map_eq f g h
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilyHom_eq_of_homotopy
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x y))

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
