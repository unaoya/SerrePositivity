module
public import SerrePositivity.KST.SConstruction.FamilyChainCompositeClasses

/-! # 全補正列の連結・前後合成と合成式
概要：全区間を保持する列の基本操作を内部 Hom の合成式に移す。
方針：元の列の帰納構造とホモトピーの前後合成の式を用いる。
規約：対象や区間を選び直さず、元の実 trace を持つ列について証明する。
使われ方：実比較複体の両側の全辺路の合成を照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 連結した全列の合成は、元の二つの全列の順序付き合成。 -/
lemma familyChainCompositeClass_append {U E : SSet.{u}} {f g h : U ⟶ E}
    (c : FamilyHomotopyChain f g) (d : FamilyHomotopyChain g h) :
    familyChainCompositeClass (familyHomotopyChainAppend c d) =
      familyChainCompositeClass c ≫ familyChainCompositeClass d := by
  induction c with
  | nil => exact (Category.id_comp _).symm
  | cons H tail ih =>
      change _ ≫ familyChainCompositeClass (familyHomotopyChainAppend tail d) = _
      rw [ih]
      exact (Category.assoc _ _ _).symm

/-- 元の単一区間の合成式は同じ実辺。 -/
lemma familyChainCompositeClass_single {U E : SSet.{u}} {f g : U ⟶ E}
    (H : SSet.Homotopy f g) :
    familyChainCompositeClass (familyHomotopyChainSingle H) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) :=
  Category.comp_id _

/-- 全区間の射影は、内部 Hom の同じ後合成の関手の作用。 -/
lemma familyChainCompositeClass_map {U E B : SSet.{u}} {f g : U ⟶ E}
    (c : FamilyHomotopyChain f g) (p : E ⟶ B) :
    familyChainCompositeClass (familyHomotopyChainMap c p) =
      (hoFunctor.map ((ihom U).map p)).toFunctor.map (familyChainCompositeClass c) := by
  induction c with
  | nil =>
      simp only [familyHomotopyChainMap, familyChainCompositeClass,
        CategoryTheory.Functor.map_id]
      rfl
  | cons H tail ih =>
      change _ ≫ familyChainCompositeClass (familyHomotopyChainMap tail p) = _
      rw [ih, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom, ← CategoryTheory.Functor.map_comp]
      rfl

/-- 全区間のパラメータ制限は、内部 Hom の同じ前合成の関手の作用。 -/
lemma familyChainCompositeClass_precomp {T U E : SSet.{u}} (j : T ⟶ U) {f g : U ⟶ E}
    (c : FamilyHomotopyChain f g) :
    familyChainCompositeClass (familyHomotopyChainPrecomp j c) =
      (hoFunctor.map ((pre j).app E)).toFunctor.map (familyChainCompositeClass c) := by
  induction c with
  | nil =>
      simp only [familyHomotopyChainPrecomp, familyChainCompositeClass,
        CategoryTheory.Functor.map_id]
      rfl
  | cons H tail ih =>
      change _ ≫ familyChainCompositeClass (familyHomotopyChainPrecomp j tail) = _
      rw [ih, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp_hom, ← CategoryTheory.Functor.map_comp]
      rfl

end SerrePositivity.KST.SConstruction
