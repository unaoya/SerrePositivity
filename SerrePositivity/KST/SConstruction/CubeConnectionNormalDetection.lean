module
public import SerrePositivity.KST.SConstruction.CubeConnectionNormal

/-! # ブロック標準表示の元の頂点関数による検出
概要：入力の出力ブロックと、その fiber max の関数から標準表示を一意に回収する。
方針：最初の二入力が同じブロックかで開始・結合を分離し、一座標頂点で fiber を検出する。
規約：空の立方体も含む。使われ方：max の語の元の Serre 評価の等号。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 各入力の出力ブロックは、標準表示を一意に決める。 -/
lemma cubeConnectionNormalBlock_injective (n m : ℕ) :
    Function.Injective (cubeConnectionNormalBlock (n := n) (m := m)) := by
  induction n generalizing m with
  | zero => intro d e h; cases d; cases e; rfl
  | succ n ih =>
    intro d e h
    cases d with
    | keep d =>
      cases e with
      | keep e =>
        congr 1
        apply ih
        funext i
        simpa only [cubeConnectionNormalBlock, Fin.cons_succ, Fin.succ_inj] using
          congrFun h i.succ
      | merge e =>
        cases n with
        | zero => cases e
        | succ n =>
          have hc := congrFun h (0 : Fin (n + 1)).succ
          simp only [cubeConnectionNormalBlock, Fin.cons_succ,
            cubeConnectionNormalBlock_zero] at hc
          exact False.elim ((Fin.succ_ne_zero _) hc)
    | merge d =>
      cases e with
      | keep e =>
        cases n with
        | zero => cases d
        | succ n =>
          have hc := congrFun h (0 : Fin (n + 1)).succ
          simp only [cubeConnectionNormalBlock, Fin.cons_succ,
            cubeConnectionNormalBlock_zero] at hc
          exact False.elim ((Fin.succ_ne_zero _) hc.symm)
      | merge e =>
        congr 1
        apply ih
        funext i
        exact congrFun h i.succ

/-- 元の全頂点の fiber max は、各入力の出力先を一意に決める。 -/
lemma cubeFiberMax_injective (n m : ℕ) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax (n := n) (m := m)) := by
  intro q r h
  funext i
  have htrue : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax r (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexAtom n i) (q i) = true := by
    rw [← h]
    exact (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax_true_iff q _ _).mpr ⟨i, rfl, by simp [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexAtom]⟩
  obtain ⟨j, hj, hv⟩ := (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax_true_iff r _ _).mp htrue
  have hji : j = i := by simpa [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexAtom] using hv
  subst j
  exact hj.symm

/-- ブロック標準表示の元の全頂点での評価。 -/
def cubeConnectionNormalVertex {n m : ℕ} (d : CubeConnectionNormal n m) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax (cubeConnectionNormalBlock d)

/-- 元の頂点関数は、ブロック標準表示を一意に決める。 -/
lemma cubeConnectionNormalVertex_injective (n m : ℕ) :
    Function.Injective (cubeConnectionNormalVertex (n := n) (m := m)) := by
  intro d e h
  exact cubeConnectionNormalBlock_injective n m (cubeFiberMax_injective n m h)

/-- 一ブロックずつなら、元の全頂点での評価は恒等。 -/
lemma cubeConnectionNormalId_vertex (n : ℕ) :
    cubeConnectionNormalVertex (cubeConnectionNormalId n) = _root_.id := by
  dsimp only [cubeConnectionNormalVertex]
  rw [cubeConnectionNormalId_block, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax_id]

/-- 標準表示の隣接結合は、元の同じ connection との関数合成。 -/
lemma cubeConnectionNormalVertex_connect {n m : ℕ} (d : CubeConnectionNormal n (m + 2))
    (i : Fin (m + 1)) :
    cubeConnectionNormalVertex (cubeConnectionNormalConnect d i) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection m i ∘ cubeConnectionNormalVertex d := by
  dsimp only [cubeConnectionNormalVertex]
  rw [cubeConnectionNormalConnect_block, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax_comp, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax_predAbove]

end SerrePositivity.KST.SConstruction
