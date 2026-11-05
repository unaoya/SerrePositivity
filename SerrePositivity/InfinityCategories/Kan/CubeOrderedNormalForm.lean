module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Kan.CubeGeneratorSupport

/-! # 具体的な cubical 射の順序つき非交差 support
概要：元の全生成射の合成について、有限 max 表示の入力集合が出力順に並び互いに交わらない。
方針：生成射と合成で有効入力の順序を帰納し、一意な有限 max 表示へ移す。
規約：定数一と定数零の support は空集合。使われ方：正準生成語と Serre 作用の構成。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Kan
open SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の具体的な cubical 生成関数の有効入力は出力順に並ぶ。 -/
lemma cubeMapGenerated_support_ordered {n m : ℕ} {f : CubeVertex n → CubeVertex m}
    (h : CubeMapGenerated f) : CubeSupportOrdered f := by
  induction h with
  | id n => exact cubeSupportOrdered_id n
  | face b n p => exact cubeSupportOrdered_face b n p
  | degeneracy n p => exact cubeSupportOrdered_degeneracy n p
  | connection n p => exact cubeSupportOrdered_connection n p
  | comp hf hg ihf ihg => exact cubeSupportOrdered_comp hg ihf ihg

/-- 順序を保つ support では、一つの有効入力は二つの出力に現れない。 -/
lemma cubeSupportOrdered_output_unique {n m : ℕ} {f : CubeVertex n → CubeVertex m}
    (h : CubeSupportOrdered f) {i : Fin n} {j k : Fin m}
    (hj : CubeActive f i j) (hk : CubeActive f i k) : j = k := by
  rcases lt_trichotomy j k with hjk | hjk | hkj
  · exact False.elim ((lt_irrefl i) (h hjk hj hk))
  · exact hjk
  · exact False.elim ((lt_irrefl i) (h hkj hk hj))

/-- 有限 max 表示の各出力の有効入力集合。 -/
def cubeJoinNormalFormSupport {n m : ℕ} (s : CubeJoinNormalForm n m) (j : Fin m) :
    Finset (Fin n) :=
  (s j).getD ∅

/-- 元の射から回収した表示の support は、同じ射の有効入力そのもの。 -/
lemma mem_cubeJoinNormalFormSupport {n m : ℕ} (f : CubeVertex n → CubeVertex m)
    (i : Fin n) (j : Fin m) :
    i ∈ cubeJoinNormalFormSupport (cubeJoinNormalFormOfMap f) j ↔ CubeActive f i j := by
  cases hz : f ⊥ j <;>
    simp [cubeJoinNormalFormSupport, cubeJoinNormalFormOfMap, CubeActive, hz]

/-- 具体的な射の正規形の support は、元の出力順に厳密に並ぶ。 -/
lemma concreteCubeNormalForm_support_ordered {X Y : ConcreteCube} (f : X ⟶ Y)
    {j k : Fin Y.dimension} (hjk : j < k) {i l : Fin X.dimension}
    (hi : i ∈ cubeJoinNormalFormSupport (concreteCubeNormalForm f) j)
    (hl : l ∈ cubeJoinNormalFormSupport (concreteCubeNormalForm f) k) : i < l := by
  exact cubeMapGenerated_support_ordered f.property hjk
    ((mem_cubeJoinNormalFormSupport f.val i j).mp hi)
    ((mem_cubeJoinNormalFormSupport f.val l k).mp hl)

/-- 具体的な射の正規形の同じ入力は、ただ一つの出力にしか現れない。 -/
lemma concreteCubeNormalForm_support_output_unique {X Y : ConcreteCube} (f : X ⟶ Y)
    {i : Fin X.dimension} {j k : Fin Y.dimension}
    (hj : i ∈ cubeJoinNormalFormSupport (concreteCubeNormalForm f) j)
    (hk : i ∈ cubeJoinNormalFormSupport (concreteCubeNormalForm f) k) : j = k := by
  exact cubeSupportOrdered_output_unique (cubeMapGenerated_support_ordered f.property)
    ((mem_cubeJoinNormalFormSupport f.val i j).mp hj)
    ((mem_cubeJoinNormalFormSupport f.val i k).mp hk)

/-- 具体的な射の正規形の全出力の support は互いに交わらない。 -/
lemma concreteCubeNormalForm_support_pairwise_disjoint {X Y : ConcreteCube} (f : X ⟶ Y) :
    Pairwise (fun j k => Disjoint
      (cubeJoinNormalFormSupport (concreteCubeNormalForm f) j)
      (cubeJoinNormalFormSupport (concreteCubeNormalForm f) k)) := by
  intro j k hjk
  apply Finset.disjoint_left.mpr
  intro i hi hk
  exact hjk (concreteCubeNormalForm_support_output_unique f hi hk)

end SerrePositivity.InfinityCategories.Kan

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeNormalForm_support_ordered := _root_.SerrePositivity.InfinityCategories.Kan.concreteCubeNormalForm_support_ordered

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeNormalForm_support_output_unique := _root_.SerrePositivity.InfinityCategories.Kan.concreteCubeNormalForm_support_output_unique

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeNormalForm_support_pairwise_disjoint := _root_.SerrePositivity.InfinityCategories.Kan.concreteCubeNormalForm_support_pairwise_disjoint

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cubeJoinNormalFormSupport (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeJoinNormalFormSupport := _root_.SerrePositivity.InfinityCategories.Kan.cubeJoinNormalFormSupport

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeMapGenerated_support_ordered := _root_.SerrePositivity.InfinityCategories.Kan.cubeMapGenerated_support_ordered

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeSupportOrdered_output_unique := _root_.SerrePositivity.InfinityCategories.Kan.cubeSupportOrdered_output_unique

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.mem_cubeJoinNormalFormSupport := _root_.SerrePositivity.InfinityCategories.Kan.mem_cubeJoinNormalFormSupport

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeJoinNormalFormSupport.eq_1 := _root_.SerrePositivity.InfinityCategories.Kan.cubeJoinNormalFormSupport.eq_1
