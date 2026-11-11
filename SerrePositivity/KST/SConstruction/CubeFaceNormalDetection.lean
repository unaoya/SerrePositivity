module
public import SerrePositivity.KST.SConstruction.CubeFaceNormal

/-! # 面の定数・保持標準表示の検出
概要：元の全頂点での関数は、定数・保持による標準表示を一意に決める。
方針：零頂点と一座標頂点で定数と入力保持を分離し、残りの出力で帰納する。
規約：定数零・一を区別し、零入力も含む。使われ方：面の語の Serre 表示非依存性。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の全頂点の関数は、定数・保持の標準表示を一意に決める。 -/
lemma cubeFaceNormalVertex_injective (n m : ℕ) :
    Function.Injective (cubeFaceNormalVertex (n := n) (m := m)) := by
  induction m generalizing n with
  | zero => intro d e h; cases d; cases e; rfl
  | succ m ih =>
    intro d e h
    cases d with
    | point b d =>
      cases e with
      | point c e =>
        have hb : b = c := congrFun (congrFun h ⊥) 0
        have hd : d = e := by
          apply ih
          funext x j
          simpa only [cubeFaceNormalVertex, Fin.cons_succ] using congrFun (congrFun h x) j.succ
        cases hb
        cases hd
        rfl
      | keep e =>
        have hzero := congrFun (congrFun h ⊥) 0
        have hatom := congrFun (congrFun h (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexAtom _ 0)) 0
        cases b <;> simp [cubeFaceNormalVertex, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexAtom] at hzero hatom
    | keep d =>
      cases e with
      | point c e =>
        have hzero := congrFun (congrFun h ⊥) 0
        have hatom := congrFun (congrFun h (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexAtom _ 0)) 0
        cases c <;> simp [cubeFaceNormalVertex, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexAtom] at hzero hatom
      | keep e =>
        have hd : d = e := by
          apply ih
          funext x j
          simpa only [cubeFaceNormalVertex, Fin.cons_succ] using
            congrFun (congrFun h (Fin.cons false x)) j.succ
        cases hd
        rfl

end SerrePositivity.KST.SConstruction
