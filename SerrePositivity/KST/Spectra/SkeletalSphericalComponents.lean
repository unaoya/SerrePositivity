module

public import SerrePositivity.KST.Spectra.SkeletalFiberComponents
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.SkeletalSphericalCochain

/-!
概要：骨格上の球面的係数を同じ境界定数単体で fiber の成分へ実現する。
方針：各代表を球面へ降ろし、セルの族として fiber の頂点へ束ねる。
規約：元の骨格の射との制限の一致と塔の微分の同定は別途証明する。
使われ方：Goerss–Jardine I §7、VIII §1。幾何的係数と成分係数の代表の比較。
-/

@[expose] public section

universe u
open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：セルごとの境界定数単体を実際の fiber の頂点として実現する。
方針：標準球面からの射をセル球面へ移し、fiber の逆同型へ渡す。
規約：代表を選び直さず、指定した単体をそのまま使う。
使われ方：Goerss–Jardine VIII §1。cochain の代表と成分の代表の共有。 -/
def stageFiberSimplexVertex (K : SSet.{u}) (Y : PointedSimplicialSet.{u}) (n : ℕ)
    (a : K.nonDegenerate (n + 1) → Y.right.PtSimplex (n + 1) Y.basepoint) :
    (UnbasedPointedMapping.stageFiber K Y n).right _⦋0⦌ :=
  stageFiberVertex K Y n (fun s ↦ (SimplexCell.sphereIso.{u} (n + 1)).hom ≫
    (SphereSimplex.equiv Y (n + 1)).symm (a s))

/-- 概要：境界定数単体から実現した fiber の成分係数は指定した単体の類。
方針：球面同型の往復と球面から単体への往復を消す。
規約：符号変更も代表の選び直しも行わない。
使われ方：Goerss–Jardine I §7、VIII §1。係数比較の代表公式。 -/
@[simp]
theorem stageFiberComponentEquiv_simplexVertex (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ)
    (a : K.nonDegenerate (n + 1) → Y.right.PtSimplex (n + 1) Y.basepoint)
    (s : K.nonDegenerate (n + 1)) :
    stageFiberComponentEquiv K Y n (π₀.mk (stageFiberSimplexVertex K Y n a)) s =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (a s) := by
  rw [stageFiberSimplexVertex, stageFiberComponentEquiv_vertex,
    Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]

/-- 概要：骨格上の射から取った代表の fiber 実現は元の cochain と同じ係数を持つ。
方針：各非退化単体で同一の境界定数単体を使う。
規約：低次元の定数条件は既存の cochain の条件をそのまま用いる。
使われ方：Goerss–Jardine VIII §1。骨格の幾何的係数と成分係数の比較。 -/
theorem simplexVertex_cochain (K : SSet.{u}) (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (n : ℕ)
    (f : (K.skeleton (n + 3) : SSet.{u}) ⟶ Y.right)
    (h : ∀ s : (K.skeleton (n + 3) : SSet.{u}) _⦋n + 1⦌,
      yonedaEquiv.symm s ≫ f = SSet.const Y.basepoint) :
    (fun s ↦ Additive.ofMul (stageFiberComponentEquiv K Y (n + 1)
      (π₀.mk (stageFiberSimplexVertex K Y (n + 1)
        (fun t ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.simplexValue f h t.val))) s)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cochain f h := by
  funext s
  rw [stageFiberComponentEquiv_simplexVertex]
  rfl

end

end SerrePositivity.KST.Spectra.SkeletalCellAttachment
