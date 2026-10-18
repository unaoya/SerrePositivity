module
public import SerrePositivity.KST.ProExcision.BlockInsertionFixed
public import Mathlib.Algebra.Group.TypeTags.Hom

/-!
# イデアル内の補助列の群準同型

概要：両側イデアル内の列ベクトルの群を実三角ブロック群へ送る。
方針：係数の加法群の包含を乗法タグへ移し、証明済みの補助列の群準同型を制限する。
規約：KST Lemma 4.16 の Q=M_{n,1}(I)、μ 版 A.5 の因子内入力。
使われ方：μ の第二因子を H の中の実群準同型として与える。
-/
@[expose] public noncomputable section
universe u v
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} [Ring R]

/-- 概要：イデアル内のベクトルの係数の包含は加法群準同型。
方針：各成分の部分加法群の包含を使う。
規約：KST 4.16 の Q。使われ方：補助列の準同型の定義域の制限。 -/
def idealVectorInclusion (J : TwoSidedIdeal R) (ι : Type v) : (ι → J) →+ (ι → R) where
  toFun v i := v i
  map_zero' := rfl
  map_add' _ _ := rfl

/-- 概要：イデアル内の列ベクトルは補助列として実三角ブロック群に入る。
方針：補助列の準同型を係数の包含に前合成し、値域を実群に制限する。
規約：KST Lemma 4.16 の ψ、非可換な係数イデアル。
使われ方：μ 版 A.5 の第二因子 Q→H。 -/
def idealBlockColumnHom {ι : Type v} [Fintype ι]
    (n m : ℕ) (J : TwoSidedIdeal R) (r : ι → Fin (n + m)) (p : Fin (n + m))
    (hr : ∀ i, r i < p) (hp : n ≤ p.val) :
    Multiplicative (ι → J) →* triangularBlockGroup n m J :=
  ((blockColumnHom r p (fun i ↦ (hr i).ne')).comp
    (idealVectorInclusion J ι).toMultiplicative).codRestrict
      (triangularBlockGroup n m J) (fun v ↦
        blockColumnHom_mem_triangularBlockGroup n m J r p hr hp
          ((idealVectorInclusion J ι).toMultiplicative v) (fun i ↦ (v.toAdd i).property))

end SerrePositivity.KST.ProExcision
