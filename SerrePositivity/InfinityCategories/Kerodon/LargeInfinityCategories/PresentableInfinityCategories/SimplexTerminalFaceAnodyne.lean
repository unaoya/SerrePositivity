module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.NerveInitialComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexCellIndex

/-!
概要：終頂点を保つ単射な標準単体の面は right anodyne。特に交互列の偶数面に適用する。
方針：同じ有限順序圏の nerve へ移し、終対象を保つ単射の一般補題を使う。
規約：元の標準単体の射そのものの anodyne 性を返す。
使われ方：偶数前置図式の分裂三角形を全交互前置図式へ持ち上げる。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


private def liftedFinLast_isTerminal (n : ℕ) :
    IsTerminal (ULift.up (Fin.last n) : ULift.{u} (Fin (n + 1))) := by
  refine IsTerminal.ofUniqueHom (fun j ↦ homOfLE (Fin.le_last j.down)) ?_
  intro j f
  exact Subsingleton.elim _ _

/-- 概要：最後の頂点を保つ単射な標準単体の射は right anodyne。
方針：標準単体と同じ有限順序の nerve の同型で移す。
規約：追加のホーン充填入力は不要。
使われ方：有限交互前置図式への制限の trivial Kan 性。 -/
lemma simplexMap_rightAnodyne_of_preservesLast {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    [Mono (SSet.stdSimplex.map α : (Δ[m] : SSet.{u}) ⟶ Δ[n])]
    (hα : α.toOrderHom (Fin.last m) = Fin.last n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions (SSet.stdSimplex.map α : (Δ[m] : SSet.{u}) ⟶ Δ[n]) := by
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSimplexCellIndex.{u} α
  let e : Arrow.mk (SSet.stdSimplex.map α : (Δ[m] : SSet.{u}) ⟶ Δ[n]) ≅
      Arrow.mk (nerveMap F) :=
    Arrow.isoMk (SSet.stdSimplex.isoNerve m) (SSet.stdSimplex.isoNerve n)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSimplexCellIndex_projection α)
  have : Mono (nerveMap F) :=
    ((MorphismProperty.monomorphisms SSet.{u}).arrow_mk_iso_iff e).mp inferInstance
  have ht : IsTerminal (F.obj (ULift.up (Fin.last m))) := by
    change IsTerminal (ULift.up (α.toOrderHom (Fin.last m)) : ULift.{u} (Fin (n + 1)))
    rw [hα]
    exact liftedFinLast_isTerminal n
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions.arrow_mk_iso_iff e).mpr
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.nerveMap_preservingTerminal_rightAnodyne F (liftedFinLast_isTerminal m) ht)

/-- 概要：可算交互前置図式の偶数頂点を選ぶ標準単体の面。
方針：有限順序の頂点 i を 2i へ送る。
規約：最後の頂点も保持する。
使われ方：元の表示前置図式と全交互前置図式の比較。 -/
def sequentialEvenFace (n : ℕ) : ⦋n⦌ ⟶ ⦋2 * n⦌ :=
  SimplexCategory.Hom.mk (a := ⦋n⦌) (b := ⦋2 * n⦌)
    { toFun := fun i : Fin (n + 1) ↦ (⟨2 * i.val, by omega⟩ : Fin (2 * n + 1))
      monotone' := by intro i j h; change 2 * i.val ≤ 2 * j.val; omega }

instance sequentialEvenFace_mono (n : ℕ) : Mono (sequentialEvenFace n) := by
  rw [SimplexCategory.mono_iff_injective]
  intro i j h
  apply Fin.ext
  have h' := congrArg Fin.val h
  change 2 * i.val = 2 * j.val at h'
  omega

instance sequentialEvenFace_map_mono (n : ℕ) :
    Mono (SSet.stdSimplex.map (sequentialEvenFace n) : (Δ[n] : SSet.{u}) ⟶ Δ[2 * n]) := by
  rw [NatTrans.mono_iff_mono_app]
  intro d
  rw [mono_iff_injective]
  intro x y h
  apply SSet.stdSimplex.objEquiv.injective
  have h' := congrArg SSet.stdSimplex.objEquiv h
  change SSet.stdSimplex.objEquiv x ≫ sequentialEvenFace n =
    SSet.stdSimplex.objEquiv y ≫ sequentialEvenFace n at h'
  exact (cancel_mono (sequentialEvenFace n)).mp h'

/-- 概要：偶数前置面は元の標準単体への right anodyne 包含。
方針：単射性と終頂点の保持を一般の標準単体の判定へ渡す。
規約：次数零を含む。
使われ方：既存の全交互前置図式を保つ持ち上げ。 -/
lemma sequentialEvenFace_rightAnodyne (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions (SSet.stdSimplex.map (sequentialEvenFace n) :
      (Δ[n] : SSet.{u}) ⟶ Δ[2 * n]) := by
  apply simplexMap_rightAnodyne_of_preservesLast
  apply Fin.ext
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
