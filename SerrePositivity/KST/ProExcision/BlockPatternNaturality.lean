module
public import SerrePositivity.KST.ProExcision.BlockPatternColumn

/-!
# 実三角ブロック群の係数に関する自然性

概要：係数イデアルを保つ単位環準同型は三角ブロック群の準同型を誘導する。
方針：行列の各成分と単位の 1 からの差に係数準同型を適用する。
規約：KST Lemma 4.16 の (I,a) に関する関手性の係数部分。
使われ方：非単位環の単位化と、単体環の各面・退化写像への移送。
-/
@[expose] public noncomputable section
universe u v
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} {R' : Type v} [Ring R] [Ring R']

/-- 概要：部分環を保つ単位環準同型は差の単位部分群の準同型を誘導する。
方針：単位群への写像と差の保存を使い、逆にも同じ条件を適用する。
規約：KST 4.16、実群模型の係数変更。
使われ方：三角ブロック群の係数準同型。 -/
def oneDifferenceSubgroupMap (S : NonUnitalSubring R) (S' : NonUnitalSubring R')
    (f : R →+* R') (hf : ∀ x, x ∈ S → f x ∈ S') :
    oneDifferenceSubgroup S →* oneDifferenceSubgroup S' where
  toFun a := ⟨Units.map f.toMonoidHom a.val, by
    constructor
    · change f (a.val : R) - 1 ∈ S'
      rw [← map_one f, ← map_sub]
      exact hf _ a.property.1
    · change f ((a.val⁻¹ : Rˣ) : R) - 1 ∈ S'
      rw [← map_one f, ← map_sub]
      exact hf _ a.property.2⟩
  map_one' := by apply Subtype.ext; exact map_one (Units.map f.toMonoidHom)
  map_mul' a b := by apply Subtype.ext; exact map_mul (Units.map f.toMonoidHom) a.val b.val

/-- 概要：係数イデアルを保つ準同型は三角ブロック部分環を保つ。
方針：許されない各成分は零のままであり、許される成分はイデアルへ送られる。
規約：KST 4.16 の非可換再記述。
使われ方：単体環の各次数での行列模型の自然性。 -/
lemma map_mem_blockPattern (N n : ℕ) (J : TwoSidedIdeal R) (J' : TwoSidedIdeal R')
    (f : R →+* R') (hf : ∀ x, x ∈ J → f x ∈ J')
    {A : Matrix (Fin N) (Fin N) R} (hA : A ∈ blockPatternSubring N n J) :
    A.map f ∈ blockPatternSubring N n J' := by
  constructor
  · intro i j hij
    change f (A i j) = 0
    rw [hA.1 i j hij, map_zero]
  · intro i j
    exact hf _ (hA.2 i j)

/-- 概要：係数イデアルを保つ環準同型による実三角ブロック群の準同型。
方針：行列環の係数写像を差の部分群へ制限する。
規約：KST Lemma 4.16、可換性を要求しない自然性。
使われ方：非単位の単体環へ次数ごとの実群模型を組み立てる。 -/
def triangularBlockGroupMap (n m : ℕ) (J : TwoSidedIdeal R) (J' : TwoSidedIdeal R')
    (f : R →+* R') (hf : ∀ x, x ∈ J → f x ∈ J') :
    triangularBlockGroup n m J →* triangularBlockGroup n m J' :=
  oneDifferenceSubgroupMap (blockPatternSubring (n + m) n J) (blockPatternSubring (n + m) n J')
    (f.mapMatrix) (fun _ h ↦ map_mem_blockPattern (n + m) n J J' f hf h)

end SerrePositivity.KST.ProExcision
