module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinReverseBoundary
public import Mathlib.CategoryTheory.HomCongr

/-! # 錐の図式の反転

概要：図式 p の錐を反転すると、反転した図式への余錐になる。
方針：op の Hom の同値と join の反転同型を合成し、固定因子の条件へ制限する。
規約：パラメーターも反転する。使われ方：S4 の slice／coslice の双対比較。

対応節は Kerodon 7.1（Tag 02H1）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：join からの射を左右交換した反転 join から反転値域への射へ移す同値。
方針：op 関手の充満忠実性と反転 join の同型を使う。
規約：A は錐のパラメーター、K は固定図式。使われ方：固定条件への制限。 -/
def coneDiagramReverseHomEquiv (A K X : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A K ⟶ X) ≃ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K.op A.op ⟶ X.op) :=
  (SSet.opEquivalence.fullyFaithfulFunctor.homEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A K) (Y := X)).trans
    (Iso.homCongr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso A K) (Iso.refl X.op))

/-- 概要：錐の図式の反転の同値の順方向は join の逆反転同型での前合成。
方針：Hom の同値の定義を計算し、恒等射を消す。
規約：射の厳密な等式。使われ方：自然性と固定条件の計算。 -/
lemma coneDiagramReverseHomEquiv_apply (A K X : SSet.{u}) (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A K ⟶ X) :
    coneDiagramReverseHomEquiv A K X F =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso A K).inv ≫ SSet.opFunctor.map F := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso A K).inv ≫ SSet.opFunctor.map F ≫ 𝟙 X.op = _
  rw [Category.comp_id]

/-- 概要：錐の固定図式条件は反転した余錐の固定条件と同値。
方針：join の反転が左右の包含を交換する式と op の忠実性を使う。
規約：p と A は任意。使われ方：図式の反転の部分型への制限。 -/
lemma coneDiagramReverse_fixed_iff {A K X : SSet.{u}} (p : K ⟶ X) (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A K ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A K ≫ F = p) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K.op A.op ≫ coneDiagramReverseHomEquiv A K X F = SSet.opFunctor.map p := by
  rw [coneDiagramReverseHomEquiv_apply, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverse_inl_inv,
    ← SSet.opFunctor.map_comp]
  constructor
  · exact congrArg SSet.opFunctor.map
  · exact SSet.opEquivalence.fullyFaithfulFunctor.map_injective

/-- 概要：図式 p の A を頂点側の形状とする錐と、反転した図式への A.op の余錐は同値。
方針：join からの射の反転の同値を固定図式の条件へ制限する。
規約：値域に quasicategory 性を仮定しない。使われ方：slice の反転の各次数の同値。 -/
def coneDiagramReverseEquiv {K X : SSet.{u}} (p : K ⟶ X) (A : SSet.{u}) :
    {F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A K ⟶ X // _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A K ≫ F = p} ≃
      {G : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K.op A.op ⟶ X.op // _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K.op A.op ≫ G = SSet.opFunctor.map p} :=
  (coneDiagramReverseHomEquiv A K X).subtypeEquiv (coneDiagramReverse_fixed_iff p)

/-- 概要：join の逆反転同型は二つの因子の射に関して自然。
方針：順方向の自然性に逆同型を合成する。
規約：反転後は因子を交換する。使われ方：パラメーターの自然性。 -/
lemma stableJoinReverse_inv_naturality {K K' L L' : SSet.{u}} (f : K ⟶ K') (g : L ⟶ L') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.opFunctor.map g) (SSet.opFunctor.map f) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso K' L').inv =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso K L).inv ≫ SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso K' L').hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverse_naturality, Iso.inv_hom_id_assoc]

/-- 概要：錐の図式の反転はパラメーターへの前合成と可換。
方針：join の逆反転同型の自然性と op の合成保存を使う。
規約：パラメーターの射も反転する。使われ方：slice の反転の単体作用。 -/
lemma coneDiagramReverseEquiv_naturality {A B K X : SSet.{u}} (p : K ⟶ X) (f : A ⟶ B)
    (F : {F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join B K ⟶ X // _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr B K ≫ F = p}) :
    (coneDiagramReverseEquiv p A
      ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 K) ≫ F.val, by
        rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp, F.property]⟩).val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K.op) (SSet.opFunctor.map f) ≫ (coneDiagramReverseEquiv p B F).val := by
  change coneDiagramReverseHomEquiv A K X (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 K) ≫ F.val) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K.op) (SSet.opFunctor.map f) ≫ coneDiagramReverseHomEquiv B K X F.val
  rw [coneDiagramReverseHomEquiv_apply, coneDiagramReverseHomEquiv_apply,
    SSet.opFunctor.map_comp]
  have h := stableJoinReverse_inv_naturality f (𝟙 K)
  simpa only [CategoryTheory.Functor.map_id, Category.assoc] using
    congrArg (fun e ↦ e ≫ SSet.opFunctor.map F.val) h.symm

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
