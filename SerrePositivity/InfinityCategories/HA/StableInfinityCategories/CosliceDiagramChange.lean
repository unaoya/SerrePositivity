module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceMap

/-! # Coslice の固定図式の等号輸送と元の余錐

概要：固定図式を等号で表示変更しても、余錐の元の射と展開した族は変わらない。
方針：固定図式の等号を帰納法で消す。
規約：任意の次数・パラメーターを扱う。使われ方：畳み込みと通常の図式制限の比較。
-/
@[expose] public section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：coslice の図式の等号輸送は各単体の元の余錐を変えない。
方針：等号を消す。
規約：次数は任意。使われ方：表示を揃えた coslice 射の外延性。 -/
lemma stableCosliceDiagramChange_val {K X : SSet.{u}} {p q : K ⟶ X}
    (h : p = q) (n : SimplexCategoryᵒᵖ) (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p).obj n) :
    ((eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder h)).app n s).val = s.val := by
  subst q
  rfl

/-- 概要：coslice の図式の等号輸送は展開した余錐族を変えない。
方針：等号を消して恒等射との合成を簡約する。
規約：パラメーターは任意。使われ方：表示変更を含む図式制限の計算。 -/
lemma stableCosliceDiagramChange_uncurry {K X A : SSet.{u}} {p q : K ⟶ X}
    (h : p = q) (v : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (v ≫ eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder h)) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry v := by
  subst q
  simp only [eqToHom_refl, Category.comp_id]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
