module
public import SerrePositivity.KST.ProExcision.TriangularLastColumn

/-!
# 実三角群からブロックと列の半直積への分解

概要：最後の補助座標を基底の三角群と列群へ分ける実準同型を構成する。
方針：左上ブロックの実射影と最終列の積の公式を束ねる。
規約：KST Claim 4.15。群状性・ホモロジーの仮定を含まない非可換な実行列計算。
使われ方：Lemma 4.16 の値域を相対半直積の実値域へ移す。
-/
@[expose] public noncomputable section
universe u
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} [Ring R]

/-- 概要：実三角群のイデアル内の列への行列作用。
方針：実行列の値に既存の全行列作用を適用する。
規約：KST Claim 4.15。使われ方：最後の補助列の半直積の作用。 -/
def triangularColumnAction (n m : ℕ) (J : TwoSidedIdeal R) :
    triangularBlockGroup n m J →* Monoid.End (Multiplicative (Fin (n + m) → J)) where
  toFun g := idealMatrixAction (n + m) J g.val.val
  map_one' := (idealMatrixAction (n + m) J).map_one
  map_mul' g h := (idealMatrixAction (n + m) J).map_mul g.val.val h.val.val

/-- 概要：三角群の列作用の明示的な作用構造。
方針：自己準同型への準同型の単位・合成・乗法保存を使う。
規約：KST Claim 4.15、大域の競合する作用インスタンスを追加しない。
使われ方：実半直積モノイドの型。 -/
@[instance_reducible] def triangularColumnActionStructure (n m : ℕ) (J : TwoSidedIdeal R) :
    MulDistribMulAction (triangularBlockGroup n m J) (Multiplicative (Fin (n + m) → J)) where
  smul g v := triangularColumnAction n m J g v
  one_smul v := by
    change triangularColumnAction n m J 1 v = v
    rw [map_one]
    rfl
  mul_smul g h v := by
    change triangularColumnAction n m J (g * h) v =
      triangularColumnAction n m J g (triangularColumnAction n m J h v)
    rw [map_mul]
    rfl
  smul_one g := map_one _
  smul_mul g v w := map_mul _ v w

/-- 概要：三角群を小さい三角群と最終列の半直積へ分解する実準同型。
方針：基底に左上ブロック、ファイバーに最終列を取り、両成分で積を検証する。
規約：KST Claim 4.15、積は (AB,v+A w) の順。
使われ方：A.4 から得た零写像の実半直積への後合成。 -/
def triangularBlockAffineSplit (n m : ℕ) (J : TwoSidedIdeal R) :
    letI := triangularColumnActionStructure n m J
    triangularBlockGroup n (m + 1) J →*
      ActionProduct (triangularBlockGroup n m J) (Multiplicative (Fin (n + m) → J)) := by
  letI := triangularColumnActionStructure n m J
  exact
    { toFun := fun g ↦ ⟨triangularBlockGroupDropLast n m J g,
        Multiplicative.ofAdd (triangularBlockGroupLastColumn n m J g)⟩
      map_one' := by
        apply ActionProduct.ext
        · exact map_one _
        · change Multiplicative.ofAdd (triangularBlockGroupLastColumn n m J 1) =
            Multiplicative.ofAdd 0
          rw [triangularBlockGroupLastColumn_one]
      map_mul' := by
        intro g h
        apply ActionProduct.ext
        · exact map_mul _ g h
        · exact congrArg Multiplicative.ofAdd (triangularBlockGroupLastColumn_mul n m J g h) }

end SerrePositivity.KST.ProExcision
