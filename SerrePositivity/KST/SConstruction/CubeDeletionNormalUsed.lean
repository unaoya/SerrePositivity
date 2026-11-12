module
public import SerrePositivity.KST.SConstruction.CubeNormalEndpoints

/-! # 削除標準表示の使用入力による検出
概要：保持する入力の真偽列から、残る次元と元の削除標準表示を回収する。
方針：零座標が保持か削除かで分離し、残りの入力へ帰納する。
規約：入力次元以外は固定しない。使われ方：三段表示の入力側の一意性。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の各入力を保持するかを表す真偽列。 -/
def cubeDeletionNormalUsed : {n m : ℕ} → _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n m → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n
  | _, _, .nil => Fin.elim0
  | _, _, .drop d => Fin.cons false (cubeDeletionNormalUsed d)
  | _, _, .keep d => Fin.cons true (cubeDeletionNormalUsed d)

/-- 元の保持入力の列は、保持添字の像そのもの。 -/
lemma cubeDeletionNormalUsed_true_iff {n m : ℕ} (d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n m) (i : Fin n) :
    cubeDeletionNormalUsed d i = true ↔ ∃ j, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalEmbedding d j = i := by
  induction d with
  | nil => exact Fin.elim0 i
  | drop d ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [cubeDeletionNormalUsed, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalEmbedding]
    · simpa only [cubeDeletionNormalUsed, Fin.cons_succ, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalEmbedding,
        Fin.succ_inj] using ih i
  | keep d ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · exact ⟨fun _ => ⟨0, rfl⟩, fun _ => rfl⟩
    · change cubeDeletionNormalUsed d i = true ↔
        ∃ j, Fin.cons (α := fun _ => Fin _) 0
          (fun k => (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalEmbedding d k).succ) j = i.succ
      rw [ih i]
      constructor
      · rintro ⟨j, hj⟩
        exact ⟨j.succ, congrArg Fin.succ hj⟩
      · rintro ⟨j, hj⟩
        refine Fin.cases (fun h => ?_) (fun j h => ?_) j hj
        · exact False.elim ((Fin.succ_ne_zero i) h.symm)
        · exact ⟨j, Fin.succ_inj.mp h⟩

/-- 使用入力の真偽列は、残す入力の次元を検出する。 -/
lemma cubeDeletionNormal_dimension_of_used {n a b : ℕ}
    (d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n a) (e : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n b)
    (h : cubeDeletionNormalUsed d = cubeDeletionNormalUsed e) : a = b := by
  induction d generalizing b with
  | nil => cases e; rfl
  | drop d ih =>
    cases e with
    | drop e => exact ih e (funext fun j => congrFun h j.succ)
    | keep e =>
      have hc := congrFun h 0
      simp [cubeDeletionNormalUsed] at hc
  | keep d ih =>
    cases e with
    | drop e =>
      have hc := congrFun h 0
      simp [cubeDeletionNormalUsed] at hc
    | keep e =>
      congr 1
      exact ih e (funext fun j => congrFun h j.succ)

/-- 同じ残余次元の削除表示は、使用入力の真偽列から一意に回収される。 -/
lemma cubeDeletionNormal_eq_of_used {n m : ℕ} (d e : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n m)
    (h : cubeDeletionNormalUsed d = cubeDeletionNormalUsed e) : d = e := by
  induction d with
  | nil => cases e; rfl
  | drop d ih =>
    cases e with
    | drop e =>
      congr 1
      exact ih e (funext fun j => congrFun h j.succ)
    | keep e =>
      have hc := congrFun h 0
      simp [cubeDeletionNormalUsed] at hc
  | keep d ih =>
    cases e with
    | drop e =>
      have hc := congrFun h 0
      simp [cubeDeletionNormalUsed] at hc
    | keep e =>
      congr 1
      exact ih e (funext fun j => congrFun h j.succ)

/-- 削除と max の元の合成で、一入力がどこかの出力を真にする条件。 -/
lemma cubeDeletionConnectionNormal_atom_true_iff {n m : ℕ}
    (r : CubeDeletionConnectionNormal n m) (i : Fin n) :
    (∃ j, cubeDeletionConnectionNormalVertex r (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexAtom n i) j = true) ↔
      cubeDeletionNormalUsed r.deletion i = true := by
  rw [cubeDeletionNormalUsed_true_iff]
  change (∃ j, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax (cubeConnectionNormalBlock r.connection)
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex r.deletion (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexAtom n i)) j = true) ↔ _
  simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax_true_iff]
  constructor
  · rintro ⟨j, k, _, hk⟩
    refine ⟨k, ?_⟩
    simpa [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateSelect, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexAtom] using hk
  · rintro ⟨k, hk⟩
    refine ⟨cubeConnectionNormalBlock r.connection k, k, rfl, ?_⟩
    simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateSelect, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexAtom, hk]

/-- 元の削除・max の頂点写像は、その使用入力を検出する。 -/
lemma cubeDeletionConnectionNormal_used_eq_of_vertex_eq {n m : ℕ}
    (r s : CubeDeletionConnectionNormal n m)
    (h : cubeDeletionConnectionNormalVertex r = cubeDeletionConnectionNormalVertex s) :
    cubeDeletionNormalUsed r.deletion = cubeDeletionNormalUsed s.deletion := by
  funext i
  apply Bool.eq_iff_iff.mpr
  rw [← cubeDeletionConnectionNormal_atom_true_iff r,
    ← cubeDeletionConnectionNormal_atom_true_iff s, h]

end SerrePositivity.KST.SConstruction
