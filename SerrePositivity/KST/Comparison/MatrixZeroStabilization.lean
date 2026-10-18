module

public import SerrePositivity.KST.Comparison.MatrixStabilization
public import SerrePositivity.KST.Comparison.MatrixSpace

/-!
# 零基点の全行列の安定化

概要：新しい行と列を零で埋める加法的な安定化を、単位とのブロック和と比較する。
方針：四つのブロックを有限集合の和の同値で移し、各係数を計算する。
規約：KST Lemma 2.13 の正次数の安定化。乗法的な安定化とは基点移動を介して一致する。
使われ方：有限 rank の高次の係数表示の rank の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory

/--
概要：新しい行と列を零で埋める行列の加法準同型。
方針：零のブロックと直和の添字の同値を使う。
規約：単位を保つ環準同型とは主張しない。
使われ方：零基点に移した行列の安定化。
-/
def matrixZeroStabilization (R : Type*) [Ring R] (r : ℕ) :
    Matrix (Fin r) (Fin r) R →+ Matrix (Fin (r + 1)) (Fin (r + 1)) R where
  toFun a := Matrix.reindex (finSumFinEquiv : Fin r ⊕ Fin 1 ≃ Fin (r + 1))
    finSumFinEquiv (Matrix.fromBlocks a 0 0 0)
  map_zero' := by
    ext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    cases i <;> cases j <;> simp [Matrix.reindex_apply, Matrix.fromBlocks]
  map_add' a b := by
    ext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    cases i <;> cases j <;> simp [Matrix.reindex_apply, Matrix.fromBlocks]

/--
概要：零の行・列の安定化は係数環の準同型と可換。
方針：全てのブロックで係数の写像と零の保存を計算する。
規約：係数環は非可換でもよい。
使われ方：全行列の台単体集合の安定化の自然性。
-/
theorem matrixZeroStabilization_map {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) (r : ℕ) (a : Matrix (Fin r) (Fin r) R) :
    f.mapMatrix (matrixZeroStabilization R r a) =
      matrixZeroStabilization S r (f.mapMatrix a) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases i <;> cases j <;>
    simp [matrixZeroStabilization, Matrix.reindex_apply, Matrix.fromBlocks]

/--
概要：単位とのブロック和の後で単位を引くと、零の行・列の安定化になる。
方針：単位の保存を使った後、四つのブロックの差を計算する。
規約：単位行列を零行列へ移す基点の平行移動との可換性。
使われ方：高次の係数群の安定化を新しい零の係数で記述する。
-/
theorem matrixStabilization_sub_one (R : Type*) [Ring R] (r : ℕ)
    (a : Matrix (Fin r) (Fin r) R) :
    matrixStabilization R r a - 1 = matrixZeroStabilization R r (a - 1) := by
  calc
    _ = matrixStabilization R r a - matrixStabilization R r 1 :=
      congrArg (fun b => matrixStabilization R r a - b) (map_one (matrixStabilization R r)).symm
    _ = _ := by
      ext i j
      obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
      obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
      cases i <;> cases j <;>
        simp [matrixStabilization, matrixBlockUnit, matrixZeroStabilization,
          Matrix.reindex_apply, Matrix.fromBlocks]

/--
概要：零の行と列を付ける全行列の単体写像。
方針：各次数の加法的安定化を使い、係数環の写像との可換性で自然性を示す。
規約：零基点を保つ写像。
使われ方：正次数のホモトピー群の安定化。
-/
def matrixZeroStabilizationMap (A : SimplicialObject RingCat.{u}) (r : ℕ) :
    matrixSpace A r ⟶ matrixSpace A (r + 1) where
  app n := TypeCat.ofHom (matrixZeroStabilization (A.obj n) r)
  naturality {m n} f := by
    apply ConcreteCategory.hom_ext
    intro a
    exact (matrixZeroStabilization_map (A.map f).hom r a).symm

end SerrePositivity.KST.Comparison
