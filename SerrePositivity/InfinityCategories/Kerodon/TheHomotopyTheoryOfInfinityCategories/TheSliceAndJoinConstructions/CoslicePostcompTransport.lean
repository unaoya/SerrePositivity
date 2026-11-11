module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Coslice
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceMap
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IntervalCosliceSource

/-! # 図式の表示を揃えた coslice の後合成

概要：固定図式の像を等号で表示し直した後合成は、射影・二段階の後合成と可換。
方針：等号輸送を含む後合成を定義し、図式の等号の帰納法と錐の展開で計算する。
規約：値域の充填性は不要。使われ方：余錐空間の表現可能な比較の自然性。

対応節は Kerodon 4.3（Tag 015M）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：後合成した固定図式を等しい図式に揃える coslice の射。
方針：通常の後合成に等号の輸送を続ける。
規約：固定図式の形状は保つ。使われ方：点の Yoneda 表示を揃えた比較。 -/
def stableCoslicePostcomp {K E F : SSet.{u}} (a : K ⟶ E) (f : E ⟶ F)
    (b : K ⟶ F) (h : a ≫ f = b) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder b :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp a f ≫ eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder h)

/-- 概要：図式表示を揃えた後合成は終点射影と可換。
方針：等号の帰納法で通常の後合成の式に戻す。
規約：厳密な等号。使われ方：底の頂点 fiber への制限。 -/
lemma stableCoslicePostcomp_projection {K E F : SSet.{u}} (a : K ⟶ E) (f : E ⟶ F)
    (b : K ⟶ F) (h : a ≫ f = b) :
    stableCoslicePostcomp a f b h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection b = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a ≫ f := by
  subst b
  simpa only [stableCoslicePostcomp, eqToHom_refl, Category.comp_id] using
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderPostcomp_projection a f

/-- 概要：図式表示を揃えた後合成は任意の余錐族の後合成を表す。
方針：表示の等号を消して curry と uncurry の自然性を使う。
規約：余錐族のパラメータは任意。使われ方：比較 span の可換性。 -/
lemma stableCoslicePostcomp_uncurry {K E F T : SSet.{u}} (a : K ⟶ E) (f : E ⟶ F)
    (b : K ⟶ F) (h : a ≫ f = b) (t : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (t ≫ stableCoslicePostcomp a f b h) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry t ≫ f := by
  subst b
  simpa only [stableCoslicePostcomp, eqToHom_refl, Category.comp_id] using
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_postcomp t f

/-- 概要：二段階の後合成と図式表示の変更は合成した関手による一段階の操作に一致する。
方針：余錐を join からの射として展開し、合成の結合則を使う。
規約：途中と最後の表示の等号は任意。使われ方：fiber の二つの射影の同時比較。 -/
lemma stableCoslicePostcomp_comp {K E F G : SSet.{u}} (a : K ⟶ E) (f : E ⟶ F)
    (b : K ⟶ F) (h : a ≫ f = b) (g : F ⟶ G) (d : K ⟶ G) (j : b ≫ g = d) :
    stableCoslicePostcomp a f b h ≫ stableCoslicePostcomp b g d j =
      stableCoslicePostcomp a (f ≫ g) d (by rw [← Category.assoc, h, j]) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_injective d
  rw [stableCoslicePostcomp_uncurry]
  have h₁ := stableCoslicePostcomp_uncurry a f b h (𝟙 _)
  have h₂ := stableCoslicePostcomp_uncurry a (f ≫ g) d
    (by rw [← Category.assoc, h, j]) (𝟙 _)
  simp only [Category.id_comp] at h₁ h₂
  rw [h₁, h₂, Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
