module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FixedCosliceReindex
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitReindex

/-! # 固定図式の再添字付けと余錐族の展開

概要：同じ図式上で定義した再添字付けは、余錐族を展開すると join の左因子の前合成となる。
方針：通常の制限と図式の等号輸送に分解し、等号輸送は錐の値を変えないことを使う。
規約：パラメータは任意。使われ方：対称 span の二枝の交換の計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：固定図式の等号輸送は各次数で錐の値を変えない。
方針：図式の等号を消す。
規約：余錐の形状と値域は固定。使われ方：通常の制限と固定図式内の再添字付けの同定。 -/
lemma stableCosliceChange_val {K X : SSet.{u}} {p q : K ⟶ X} (h : p = q)
    (n : ℕ) (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) _⦋n⦌) :
    ((eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder h)).app (Opposite.op ⦋n⦌) s).val = s.val := by
  subst q
  rfl

/-- 概要：固定図式の自己作用は通常の形状制限と図式の等号輸送の合成。
方針：各次数の錐の値を比較する。
規約：全単体で厳密。使われ方：展開した余錐の自然性の再利用。 -/
lemma fixedCosliceReindex_eq_restrict {K X : SSet.{u}} (p : K ⟶ X) (i : K ⟶ K)
    (hi : i ≫ p = p) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.fixedCosliceReindex p i hi =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict p i ≫ eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder hi) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  exact (stableCosliceChange_val hi n ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict p i).app (Opposite.op ⦋n⦌) s)).symm

/-- 概要：図式の等号輸送は展開した余錐族を変えない。
方針：図式の等号を消す。
規約：余錐族のパラメータは任意。使われ方：再添字付けの展開の公式。 -/
lemma stableCosliceChange_uncurry {K X T : SSet.{u}} {p q : K ⟶ X} (h : p = q)
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (a ≫ eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder h)) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry a := by
  subst q
  simp only [eqToHom_refl, Category.comp_id]

/-- 概要：固定図式上での再添字付けは展開後の join の左因子での前合成。
方針：通常の制限に分解し、図式の等号輸送を除く。
規約：値域に充填性を仮定しない。使われ方：二枝交換の実際の作用の計算。 -/
lemma fixedCosliceReindex_uncurry {K X T : SSet.{u}} (p : K ⟶ X) (i : K ⟶ K)
    (hi : i ≫ p = p) (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (a ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.fixedCosliceReindex p i hi) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry a := by
  rw [fixedCosliceReindex_eq_restrict, ← Category.assoc,
    stableCosliceChange_uncurry hi, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_restrict]

/-- 概要：終点固定余錐空間の再添字付けも展開後に同じ左因子の前合成を行う。
方針：fiber の包含を通じて coslice の自己作用へ戻す。
規約：終点は固定。使われ方：対称 span の二枝交換を余錐の等号で読む。 -/
lemma fixedCoconeMappingReindex_uncurry {K X T : SSet.{u}} (p : K ⟶ X) (i : K ⟶ K)
    (hi : i ≫ p = p) (y : X _⦋0⦌) (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry ((a ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.fixedCoconeMappingReindex p i hi y) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) y) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) y) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry ((a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) y) ≫
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.fixedCosliceReindex p i hi) = _
  exact fixedCosliceReindex_uncurry p i hi _

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
