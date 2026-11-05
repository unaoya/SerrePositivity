module

public import SerrePositivity.KST.LocalizingInvariants.ReflectiveTargetConstants
public import SerrePositivity.InfinityCategories.F1B.Fibrations.RightHomotopySquare
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.PreFiberKan

/-!
概要：全パラメータの定値関手間の Hom 比較から、元の区間写像空間の同値を得る。
方針：標的の普遍族を持ち上げて逆射を選び、両逆を h Fun の単射性で証明する。
規約：元の intervalFunctorMap 自身のホモトピー逆。使われ方：反射の局所な写像空間。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma intervalFunctorMap_equivalence_of_constantHom_bijective
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (F : X ⟶ Y) (x y : X _⦋0⦌)
    (h : ∀ (A : SSet.{u}) [Quasicategory A],
      Function.Bijective (_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.constantFunctorPostMap F A x y)) :
    IsSimplicialHomotopyEquivalence (intervalFunctorMap F x y) := by
  let K := intervalMappingSpace x y
  let L := intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) y)
  let f := intervalFunctorMap F x y
  obtain ⟨α, hα⟩ := (h L).surjective (intervalFamilyHom (𝟙 L))
  obtain ⟨g, hg⟩ := intervalFamilyHom_surjective L X x y α
  have hr : intervalFamilyHom (g ≫ f) = intervalFamilyHom (𝟙 L) := by
    rw [_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.intervalFunctorMap_familyHom_post, hg, hα]
  have hl : intervalFamilyHom (f ≫ g) = intervalFamilyHom (𝟙 K) := by
    apply (h K).injective
    rw [← _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.intervalFunctorMap_familyHom_post, ← _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.intervalFunctorMap_familyHom_post]
    have hh := congrArg (intervalFamilyHomPrecomp f) hr
    change intervalFamilyHom (f ≫ (g ≫ f)) = intervalFamilyHom (f ≫ 𝟙 L) at hh
    rw [Category.comp_id] at hh
    rw [Category.id_comp]
    simpa only [Category.assoc, f] using hh
  exact ⟨g, intervalFamilyHom_eq_imp_homotopy hl, intervalFamilyHom_eq_imp_homotopy hr⟩

end SerrePositivity.KST.LocalizingInvariants
