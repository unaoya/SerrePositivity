module

public import SerrePositivity.KST.Comparison.ComponentPointedSimplex

/-!
# 成分全体の包含は正次数のホモトピー群を保つ

概要：Kan 複体から連結成分全体を選んだ部分複体の包含は、選ばれた基点で正次数の群同型を誘導する。
方針：境界定数単体と、それらの関係を与える充填の両方を一意に持ち上げる。
規約：KST 式 (2.2)、Lemma 2.13。ホモトピー群と積は K-L9 の定義を借りる。
使われ方：ĜL の正次数の群を全行列の正次数の群に置き換える。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite SSet
open scoped Simplicial

/--
概要：包含後の境界定数単体を結ぶ RelStruct は選んだ部分複体へ持ち上がる。
方針：充填の一つの面が部分複体に属することから充填を持ち上げ、包含後で全ての面を検査する。
規約：Kan 性はこの代表の持ち上げには不要。
使われ方：包含による正次数のホモトピー群の単射性。
-/
def componentRelStructLift (X : SSet.{u}) (P : π₀ X → Prop)
    (x : (componentSubcomplex X P : SSet) _⦋0⦌) {n : ℕ}
    {f g : (componentSubcomplex X P : SSet).PtSimplex (n + 1) x} {i : Fin (n + 2)}
    (r : PtSimplex.RelStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (componentSubcomplex X P).ι rfl f)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (componentSubcomplex X P).ι rfl g) i) :
    PtSimplex.RelStruct f g i where
  map := componentSimplexLift X P r.map
    (simplex_in_component_of_face X P r.map i.castSucc f.map r.δ_castSucc_map)
  δ_castSucc_map := by
    apply (cancel_mono (componentSubcomplex X P).ι).mp
    rw [Category.assoc, componentSimplexLift_ι]
    exact r.δ_castSucc_map
  δ_succ_map := by
    apply (cancel_mono (componentSubcomplex X P).ι).mp
    rw [Category.assoc, componentSimplexLift_ι]
    exact r.δ_succ_map
  δ_map_of_lt j hj := by
    apply (cancel_mono (componentSubcomplex X P).ι).mp
    rw [Category.assoc, componentSimplexLift_ι, r.δ_map_of_lt j hj, SSet.const_comp]
  δ_map_of_gt j hj := by
    apply (cancel_mono (componentSubcomplex X P).ι).mp
    rw [Category.assoc, componentSimplexLift_ι, r.δ_map_of_gt j hj, SSet.const_comp]

/--
概要：成分全体の包含が誘導する正次数のホモトピー群の写像は全単射。
方針：全射性は代表単体の持ち上げ、単射性は関係の充填の持ち上げを使う。
規約：次数の添字 n は実際の次数 n+1。
使われ方：可逆成分から全行列への正次数の比較。
-/
theorem componentHomotopyMap_bijective (X : SSet.{u}) [KanComplex X]
    (P : π₀ X → Prop) (x : (componentSubcomplex X P : SSet) _⦋0⦌) (n : ℕ) :
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := n)
      (componentSubcomplex X P).ι (x := x) rfl) := by
  constructor
  · intro a b hab
    induction a using Quotient.inductionOn with | h f => ?_
    induction b using Quotient.inductionOn with | h g => ?_
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (componentSubcomplex X P).ι rfl f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (componentSubcomplex X P).ι rfl g) := hab
    obtain ⟨r⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexRel_iff_relStruct (0 : Fin (n + 2))).1
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk_eq_iff _ _).1 he)
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.sound (componentRelStructLift X P x r)
  · intro a
    induction a using Quotient.inductionOn with | h s => ?_
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (componentPtSimplexLift X P x s), ?_⟩
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex
      (componentSubcomplex X P).ι rfl (componentPtSimplexLift X P x s)) = _
    rw [componentPtSimplexLift_map]
    rfl

/--
概要：選ばれた基点における成分部分複体と元の Kan 複体の正次数の群同型。
方針：包含の誘導準同型と全単射性を組み合わせる。
規約：KST Lemma 2.13 の可逆成分の高次比較。群演算を輸送で置き換えない。
使われ方：有限 rank の ĜL と全行列のホモトピー群の比較。
-/
def componentPositiveHomotopyMulEquiv (X : SSet.{u}) [KanComplex X]
    (P : π₀ X → Prop) (x : (componentSubcomplex X P : SSet) _⦋0⦌) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (componentSubcomplex X P : SSet) n x ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x.val :=
  MulEquiv.ofBijective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (componentSubcomplex X P).ι rfl)
    (componentHomotopyMap_bijective X P x n)

end SerrePositivity.KST.Comparison
