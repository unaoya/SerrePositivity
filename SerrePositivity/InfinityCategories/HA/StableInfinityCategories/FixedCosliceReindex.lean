module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeMappingSpace
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SymmetricSpan

/-! # 固定した図式を保つ形状の再添字付け

概要：i ≫ p = p を満たす形状の自己射は coslice と終点固定余錐空間の自己射を誘導する。
方針：錐の左因子で前合成し、固定条件を同じ図式へ戻す。
規約：等号の輸送を部分型の条件に閉じ込める。使われ方：対称 span 上の二枝交換。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：固定図式を保つ形状の自己射は同じ coslice の自己射を与える。
方針：各錐の左因子を形状の射で前合成する。
規約：図式 p の型は変えない。使われ方：二枝交換の実際の自己作用。 -/
def fixedCosliceReindex {K X : SSet.{u}} (p : K ⟶ X) (i : K ⟶ K)
    (hi : i ≫ p = p) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p where
  app n := ↾fun s => ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 (stdSimplex.obj n.unop)) ≫ s.val, by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc, s.property, hi]⟩
  naturality {m n} α := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 _) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) (stdSimplex.map α.unop) ≫ s.val) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) (stdSimplex.map α.unop) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 _) ≫ s.val)
    simp only [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp, Category.comp_id]

/-- 概要：固定図式上の再添字付けは終点射影と可換。
方針：余錐頂点の右包含が左因子の前合成で変わらないことを使う。
規約：厳密な等号。使われ方：終点固定の余錐空間への制限。 -/
lemma fixedCosliceReindex_projection {K X : SSet.{u}} (p : K ⟶ X) (i : K ⟶ K)
    (hi : i ≫ p = p) : fixedCosliceReindex p i hi ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 _) ≫ s.val)) =
    SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K _ ≫ s.val)
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp]

/-- 概要：形状の自己射が対合なら同じ coslice 上の再添字付けも対合。
方針：各錐を二度前合成し、joinMap の合成則で形状の対合性を使う。
規約：値域に追加仮定なし。使われ方：二枝交換の自己同型。 -/
lemma fixedCosliceReindex_comp_self {K X : SSet.{u}} (p : K ⟶ X) (i : K ⟶ K)
    (hi : i ≫ p = p) (hii : i ≫ i = 𝟙 K) :
    fixedCosliceReindex p i hi ≫ fixedCosliceReindex p i hi = 𝟙 _ := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 _) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 _) ≫ s.val) = s.val
  rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, hii, Category.comp_id, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_id, Category.id_comp]

/-- 概要：図式を保つ形状の対合は coslice の自己同型を与える。
方針：再添字付け自体を逆に使う。
規約：実際の単体集合の同型。使われ方：余極限余錐の再添字付け後の余極限性。 -/
def fixedCosliceReindexIso {K X : SSet.{u}} (p : K ⟶ X) (i : K ⟶ K)
    (hi : i ≫ p = p) (hii : i ≫ i = 𝟙 K) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p where
  hom := fixedCosliceReindex p i hi
  inv := fixedCosliceReindex p i hi
  hom_inv_id := fixedCosliceReindex_comp_self p i hi hii
  inv_hom_id := fixedCosliceReindex_comp_self p i hi hii

/-- 概要：図式を保つ形状の再添字付けは終点固定余錐空間の自己射を与える。
方針：coslice の自己射を同じ底の fiber に制限する。
規約：終点 y は変えない。使われ方：対称 span の余錐空間の交換作用。 -/
def fixedCoconeMappingReindex {K X : SSet.{u}} (p : K ⟶ X) (i : K ⟶ K)
    (hi : i ≫ p = p) (y : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap _ _ (fixedCosliceReindex p i hi) (fixedCosliceReindex_projection p i hi) y

/-- 概要：形状の対合による余錐空間の自己射も対合である。
方針：fiber の誘導射の合成則と coslice 上の対合性を使う。
規約：値域に追加仮定なし。使われ方：交換作用が自己同型となること。 -/
lemma fixedCoconeMappingReindex_comp_self {K X : SSet.{u}} (p : K ⟶ X) (i : K ⟶ K)
    (hi : i ≫ p = p) (hii : i ≫ i = 𝟙 K) (y : X _⦋0⦌) :
    fixedCoconeMappingReindex p i hi y ≫ fixedCoconeMappingReindex p i hi y = 𝟙 _ := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) y
  simp only [fixedCoconeMappingReindex, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι]
  simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι]
  rw [Category.assoc, fixedCosliceReindex_comp_self p i hi hii, Category.comp_id,
    Category.id_comp]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
