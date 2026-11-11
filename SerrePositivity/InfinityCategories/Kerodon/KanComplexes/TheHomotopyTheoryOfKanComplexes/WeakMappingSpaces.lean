module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakWhitehead
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.HomotopyDetection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.InternalHomSwap
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：弱ホモトピー同値の Kan 標的への写像空間による判定。
方針：任意のパラメータ K の指数 Z^K を検査し、二重内部 Hom の交換で後合成へ移す。
規約：元の射の両端に Kan 性を課さない。Kan 性を使うのは標的 Z とその指数だけ。
使われ方：Kerodon Proposition 3.1.7.17（Tag 03PJ）、Quillen A の相対関手空間の比較。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 概要：単体集合の同型は連結成分の全単射を誘導する。
方針：逆射を π₀ に写し、厳密な両逆の等式を使う。
規約：元の単体集合の Kan 性は不要。
使われ方：写像空間の指数の順序を交換する同型の消去。 -/
lemma mapPiZero_bijective_of_iso {A B : SSet.{u}} (e : A ≅ B) :
    Function.Bijective (SSet.mapπ₀ e.hom) := by
  have hl : Function.LeftInverse (SSet.mapπ₀ e.inv) (SSet.mapπ₀ e.hom) := by
    intro a
    rw [← SSet.mapπ₀_comp_apply, e.hom_inv_id, SSet.mapπ₀_id_apply]
  have hr : Function.RightInverse (SSet.mapπ₀ e.inv) (SSet.mapπ₀ e.hom) := by
    intro b
    rw [← SSet.mapπ₀_comp_apply, e.inv_hom_id, SSet.mapπ₀_id_apply]
  exact ⟨hl.injective, hr.surjective⟩

/-- 概要：弱ホモトピー同値は任意の Kan 標的への写像空間のホモトピー同値を誘導する。
方針：Z^K へのホモトピー類の全単射を内部 Hom の交換で K からの全単射に移す。
規約：A、B、K は任意の単体集合で、Z にだけ Kan 性を要求する。
使われ方：Kerodon Proposition 3.1.7.17（Tag 03PJ）。 -/
@[kerodon 03PJ]
lemma IsWeakHomotopyEquivalence.precompose_kan {A B : SSet.{u}} {f : A ⟶ B}
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence f) (Z : SSet.{u}) [KanComplex Z] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence ((pre f).app Z) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isSimplicialHomotopyEquivalence_of_postcomposition_piZero_bijective
  intro K
  have h := (hf ((ihom K).obj Z)).comp
    (mapPiZero_bijective_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso K B Z))
  change Function.Bijective
    (SSet.mapπ₀ ((pre f).app ((ihom K).obj Z)) ∘
      SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso K B Z).hom) at h
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.mapPiZero_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso_pre f, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.mapPiZero_comp] at h
  exact (Function.Bijective.of_comp_iff'
    (mapPiZero_bijective_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso K A Z)) _).mp h

/-- 概要：弱ホモトピー同値は全 Kan 標的への写像空間の同値で判定できる。
方針：順方向は指数の交換、逆方向は各写像空間の π₀ の全単射を取る。
規約：元の射の単射性や quasicategory 性は不要。
使われ方：Kerodon Proposition 3.1.7.17（Tag 03PJ） の同値な表示。 -/
@[kerodon 03PJ]
lemma isWeakHomotopyEquivalence_iff_precompose_kan {A B : SSet.{u}} (f : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence f ↔
      ∀ (Z : SSet.{u}) [KanComplex Z], _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence ((pre f).app Z) :=
  ⟨IsWeakHomotopyEquivalence.precompose_kan, fun h Z _ ↦ (h Z).mapPiZero_bijective⟩

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
