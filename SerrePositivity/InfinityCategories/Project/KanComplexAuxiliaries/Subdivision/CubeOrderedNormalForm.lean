module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.CubeGeneratorSupport

/-! # 具体的な cubical 射の順序つき非交差 support
概要：元の全生成射の合成について、有限 max 表示の入力集合が出力順に並び互いに交わらない。
方針：生成射と合成で有効入力の順序を帰納し、一意な有限 max 表示へ移す。
規約：定数一と定数零の support は空集合。使われ方：正準生成語と Serre 作用の構成。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の具体的な cubical 生成関数の有効入力は出力順に並ぶ。 -/
lemma cubeMapGenerated_support_ordered {n m : ℕ} {f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m}
    (h : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated f) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeSupportOrdered f := by
  induction h with
  | id n => exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOrdered_id n
  | face b n p => exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOrdered_face b n p
  | degeneracy n p => exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOrdered_degeneracy n p
  | connection n p => exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOrdered_connection n p
  | comp hf hg ihf ihg => exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOrdered_comp hg ihf ihg

/-- 順序を保つ support では、一つの有効入力は二つの出力に現れない。 -/
lemma cubeSupportOrdered_output_unique {n m : ℕ} {f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m}
    (h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeSupportOrdered f) {i : Fin n} {j k : Fin m}
    (hj : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeActive f i j) (hk : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeActive f i k) : j = k := by
  rcases lt_trichotomy j k with hjk | hjk | hkj
  · exact False.elim ((lt_irrefl i) (h hjk hj hk))
  · exact hjk
  · exact False.elim ((lt_irrefl i) (h hkj hk hj))

/-- 有限 max 表示の各出力の有効入力集合。 -/
def cubeJoinNormalFormSupport {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m) (j : Fin m) :
    Finset (Fin n) :=
  (s j).getD ∅

/-- 元の射から回収した表示の support は、同じ射の有効入力そのもの。 -/
lemma mem_cubeJoinNormalFormSupport {n m : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m)
    (i : Fin n) (j : Fin m) :
    i ∈ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinNormalFormOfMap f) j ↔ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeActive f i j := by
  cases hz : f ⊥ j <;>
    simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinNormalFormOfMap, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeActive, hz]

/-- 具体的な射の正規形の support は、元の出力順に厳密に並ぶ。 -/
lemma concreteCubeNormalForm_support_ordered {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : X ⟶ Y)
    {j k : Fin Y.dimension} (hjk : j < k) {i l : Fin X.dimension}
    (hi : i ∈ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm f) j)
    (hl : l ∈ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm f) k) : i < l := by
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeMapGenerated_support_ordered f.property hjk
    ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mem_cubeJoinNormalFormSupport f.val i j).mp hi)
    ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mem_cubeJoinNormalFormSupport f.val l k).mp hl)

/-- 具体的な射の正規形の同じ入力は、ただ一つの出力にしか現れない。 -/
lemma concreteCubeNormalForm_support_output_unique {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : X ⟶ Y)
    {i : Fin X.dimension} {j k : Fin Y.dimension}
    (hj : i ∈ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm f) j)
    (hk : i ∈ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm f) k) : j = k := by
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOrdered_output_unique (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeMapGenerated_support_ordered f.property)
    ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mem_cubeJoinNormalFormSupport f.val i j).mp hj)
    ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mem_cubeJoinNormalFormSupport f.val i k).mp hk)

/-- 具体的な射の正規形の全出力の support は互いに交わらない。 -/
lemma concreteCubeNormalForm_support_pairwise_disjoint {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : X ⟶ Y) :
    Pairwise (fun j k => Disjoint
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm f) j)
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm f) k)) := by
  intro j k hjk
  apply Finset.disjoint_left.mpr
  intro i hi hk
  exact hjk (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm_support_output_unique f hi hk)

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
