module

public import SerrePositivity.InfinityCategories.F1B.EnrichedPrecomposition
public import SerrePositivity.InfinityCategories.F1B.AdjunctNaturality

/-!
概要：adjunct 対応のパラメータ自然性。
方針：QCat の whisker と内部 Hom の pre を照合し、双圏の自然性を移す。
規約：写像空間の比較に使うパラメータの quasicategory 性を明記する。
使われ方：Kerodon Prop 6.2.1.17、HTT §5.2。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Bicategory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
local instance qcatAdjunctParameterHomCategory (X Y : SSet.QCat.{u}) : Category.{u} (X ⟶ Y) :=
  SSet.QCat.bicategory.homCategory X Y

namespace QCatAdjunction

/-- 概要：パラメータ付き adjunct 対応は内部 Hom の前合成に自然。
方針：双圏の前合成自然性を二胞体の表示と whisker の比較で移す。
規約：パラメータ A,B は quasicategory。関手 U,V は任意。
使われ方：Kerodon Prop 6.2.1.17 の実際の写像空間の比較。 -/
lemma homEquiv_precomp {A B X Y : SSet.{u}} [Quasicategory A] [Quasicategory B]
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (a : QCatAdjunction F G) (i : A ⟶ B) (U : B ⟶ X) (V : B ⟶ Y)
    (α : (SSet.HomotopyCategory.mk (functorVertex (U ≫ F)) : hoFunctor.obj ((ihom B).obj Y)) ⟶
      SSet.HomotopyCategory.mk (functorVertex V)) :
    a.homEquiv (i ≫ U) (i ≫ V) ((hoFunctor.map ((pre i).app Y)).toFunctor.map α) =
      (hoFunctor.map ((pre i).app X)).toFunctor.map (a.homEquiv U V α) := by
  obtain ⟨α', rfl⟩ := (qcatCellEquiv (U ≫ F) V).surjective α
  rw [← qcatCell_whiskerLeft i α']
  change qcatCellEquiv _ _
      (a.homEquiv₂ (g := qcatMap (i ≫ U)) (h := qcatMap (i ≫ V)) (qcatMap i ◁ α')) =
    (hoFunctor.map ((pre i).app X)).toFunctor.map
      (qcatCellEquiv _ _ (a.homEquiv₂ (g := qcatMap U) (h := qcatMap V) α'))
  rw [← qcatCell_whiskerLeft]
  have h := bicategoryAdjunct_whiskerLeft a (qcatMap i) α'
  simp only [Bicategory.Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv,
    eqToHom_refl, Category.id_comp, Category.comp_id] at h
  exact congrArg (qcatCellEquiv (i ≫ U) ((i ≫ V) ≫ G)) h

end QCatAdjunction
end SerrePositivity.InfinityCategories
