module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FiniteSpanHornDecode

/-!
概要：標準 span ホーンと三点の有限半順序 nerve を厳密な同型で同定する。
方針：頂点番号の符号・復号の全次数の往復を確認する。
規約：指定された標準単体への包含を保持し、全ての面・退化と可換する。
使われ方：有限半順序図式の結果を元の標準 span へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-- 元の全単体を保つ、有限半順序 nerve と標準 span の同型。 -/
def finiteSpanNerveIso : nerve _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FiniteSpanIndex.{u} ≅ (horn 2 0 : SSet.{u}) where
  hom := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.finiteSpanNerveToHorn
  inv := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.finiteSpanHornToNerve
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply CategoryTheory.nerve.ext_of_isThin
    funext k
    exact _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.finiteSpanDecode_code (s.obj k)
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    apply stdSimplex.ext
    intro k
    exact _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.finiteSpanCode_decode ((stdSimplex.objEquiv s.val).toOrderHom k)

/-- 順射は、元の頂点番号を全次数で回収する。 -/
lemma finiteSpanNerveIso_hom_ι : finiteSpanNerveIso.{u}.hom ≫ (horn 2 0).ι =
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.finiteSpanNerveCode := rfl

/-- 全ての面・退化による制限を、元の単体と同じ作用素で保持する。 -/
lemma finiteSpanNerveIso_hom_naturality {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m)
    (s : (nerve _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FiniteSpanIndex.{u}).obj n) :
    finiteSpanNerveIso.hom.app m ((nerve _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FiniteSpanIndex).map α s) =
      (horn 2 0).toSSet.map α (finiteSpanNerveIso.hom.app n s) :=
  ConcreteCategory.congr_hom (finiteSpanNerveIso.hom.naturality α) s

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
