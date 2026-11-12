module
public import SerrePositivity.KST.SConstruction.CoherentPathActionConstancy
public import SerrePositivity.KST.SConstruction.CoherentSimplexCompositionEdge

/-! # 隣接頂点間の全 Path 評価は元の辺の定数族
概要：隣接する二頂点の間の native Path は二端点 Path のみであることを証明する。
方針：区間の両端の不等式で所属点を二端点に制限し、全次数の射列を比較する。
規約：元の ULift の宇宙を保ち、対象の Kan 性は要求しない。
使われ方：上下の prism の縦部分を元の構造射の定数族へ照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 隣接する二頂点の間では、native Path の所属点は二端点に限られる。 -/
lemma coherentAdjacentPath_mem {n : ℕ} (i : Fin (n + 1))
    (p : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) (ULift.up i.succ))
    {x : ULift.{u} (Fin (n + 2))} (hx : x ∈ p.I) :
    x = ULift.up i.castSucc ∨ x = ULift.up i.succ := by
  have h₀ := p.left_le x hx
  have h₁ := p.le_right x hx
  change i.castSucc ≤ x.down at h₀
  change x.down ≤ i.succ at h₁
  by_cases h : x.down.val = i.val
  · exact Or.inl (ULift.ext (Fin.ext h))
  · apply Or.inr
    apply ULift.ext
    apply Fin.ext
    simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ] at h₀ h₁
    simp only [Fin.val_succ]
    omega

/-- 隣接頂点の間の native Path は唯一である。 -/
instance coherentAdjacentPath_subsingleton {n : ℕ} (i : Fin (n + 1)) :
    Subsingleton (Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) (ULift.up i.succ)) := by
  constructor
  intro p q
  apply SimplicialThickening.Path.ext
  ext x
  constructor
  · intro hx
    rcases coherentAdjacentPath_mem i p hx with rfl | rfl
    · exact q.left
    · exact q.right
  · intro hx
    rcases coherentAdjacentPath_mem i q hx with rfl | rfl
    · exact p.left
    · exact p.right

/-- 隣接区間の全高次 Path における値は、元の同じ辺の作用だけで決まる。 -/
lemma coherentAdjacentPathValues_eq {n : ℕ} (i : Fin (n + 1)) {X : SSet.{u}}
    (m : nerve (Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) (ULift.up i.succ)) ⟶ X)
    (d : ℕ) (P Q : (nerve (Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up i.succ))) _⦋d⦌) :
    m.app (Opposite.op ⦋d⦌) P = m.app (Opposite.op ⦋d⦌) Q := by
  have h : P = Q := by
    refine CategoryTheory.Functor.ext (fun _ => Subsingleton.elim _ _) ?_
    intro a b f
    apply InducedCategory.hom_ext
    exact Subsingleton.elim _ _
  rw [h]

/-- 隣接区間の任意の全 Path 評価は、元の二端点 Path の値の定数族そのもの。 -/
lemma coherentAdjacentPathMap_eq_const {n : ℕ} (i : Fin (n + 1)) {X : SSet.{u}}
    (m : nerve (Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) (ULift.up i.succ)) ⟶ X) :
    m = SSet.const (m.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentEndpointPath
      (show (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) ≤ ULift.up i.succ from
        Fin.castSucc_le_succ i)))) := by
  apply coherentPathMap_eq_const
  exact coherentAdjacentPathValues_eq i m

end SerrePositivity.KST.SConstruction
