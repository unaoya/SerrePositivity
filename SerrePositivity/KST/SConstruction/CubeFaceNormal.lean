module
public import SerrePositivity.KST.SConstruction.CubeDeletionPathIndependence

/-! # 面の語の定数・保持標準表示
概要：各出力を右端から定数零・定数一・次の入力の保持として表す。
方針：標準表示の評価と、任意座標の面挿入による標準表示の更新を構成する。
規約：元の入力順を保つ。使われ方：面のみの語の Serre 評価の表示非依存性。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 出力ごとの定数または次の入力の保持による面の標準表示。 -/
inductive CubeFaceNormal : ℕ → ℕ → Type
  | nil : CubeFaceNormal 0 0
  | point {n m : ℕ} (b : Bool) (d : CubeFaceNormal n m) : CubeFaceNormal n (m + 1)
  | keep {n m : ℕ} (d : CubeFaceNormal n m) : CubeFaceNormal (n + 1) (m + 1)

/-- 定数・保持標準表示の元の全頂点での評価。 -/
def cubeFaceNormalVertex : {n m : ℕ} → CubeFaceNormal n m → (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m)
  | _, _, .nil => _root_.id
  | _, _, .point b d => fun x => Fin.cons b (cubeFaceNormalVertex d x)
  | _, _, .keep d => fun x => Fin.cons (x 0) (cubeFaceNormalVertex d (fun j => x j.succ))

/-- 全入力を保持する面の標準表示。 -/
def cubeFaceNormalId : (n : ℕ) → CubeFaceNormal n n
  | 0 => .nil
  | n + 1 => .keep (cubeFaceNormalId n)

/-- 全入力を保持する面の標準表示は元の恒等関数。 -/
lemma cubeFaceNormalId_vertex (n : ℕ) :
    cubeFaceNormalVertex (cubeFaceNormalId n) = _root_.id := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext x j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [cubeFaceNormalId, cubeFaceNormalVertex]
    · simp [cubeFaceNormalId, cubeFaceNormalVertex, ih]

/-- 元の一つの面を標準表示へ挿入する。 -/
def cubeFaceNormalInsert : {n m : ℕ} → CubeFaceNormal n m → Bool →
    Fin (m + 1) → CubeFaceNormal n (m + 1)
  | _, _, .nil, b, _ => .point b .nil
  | _, _, .point c d, b, i =>
      Fin.cases (.point b (.point c d)) (fun j => .point c (cubeFaceNormalInsert d b j)) i
  | _, _, .keep d, b, i =>
      Fin.cases (.point b (.keep d)) (fun j => .keep (cubeFaceNormalInsert d b j)) i

/-- 標準表示への面挿入は、元の同じ座標の面との関数合成を回収する。 -/
lemma cubeFaceNormalInsert_vertex {n m : ℕ} (d : CubeFaceNormal n m)
    (b : Bool) (i : Fin (m + 1)) :
    cubeFaceNormalVertex (cubeFaceNormalInsert d b i) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace b m i ∘ cubeFaceNormalVertex d := by
  induction d generalizing b with
  | nil =>
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    funext x
    simp [cubeFaceNormalInsert, cubeFaceNormalVertex, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace, Fin.insertNth_zero']
  | point c d ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · funext x
      simp [cubeFaceNormalInsert, cubeFaceNormalVertex, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace, Fin.insertNth_zero']
    · funext x
      simpa [cubeFaceNormalInsert, cubeFaceNormalVertex, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace,
        Fin.insertNth_succ_cons] using
          congrArg (fun (v : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex _) => Fin.cons (α := fun _ => Bool) c v)
            (congrFun (ih b i) x)
  | keep d ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · funext x
      simp [cubeFaceNormalInsert, cubeFaceNormalVertex, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace, Fin.insertNth_zero']
    · funext x
      simpa [cubeFaceNormalInsert, cubeFaceNormalVertex, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace,
        Fin.insertNth_succ_cons] using
          congrArg (fun (v : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex _) => Fin.cons (α := fun _ => Bool) (x 0) v)
            (congrFun (ih b i) (fun j => x j.succ))

end SerrePositivity.KST.SConstruction
