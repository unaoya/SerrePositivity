module

public import SerrePositivity.BhattScholze.DeltaAdicQuotient
public import Mathlib.RingTheory.AdicCompletion.Algebra

/-! # 古典的I進完備化上のδ写像の座標構成

MathlibのCauchy列・古典的完備化を使い、一段ずらしたδ列から写像を構成する。
導来完備化との比較はこのモジュールの対象外。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.DeltaStructure
open AdicCompletion
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

/-- 一段ずらしたδ列は再びI進Cauchy列。 -/
def adicDeltaSequence (D : DeltaStructure p R) (I : Ideal R) (hp : (p : R) ∈ I)
    (f : AdicCauchySequence I R) : AdicCauchySequence I R :=
  ⟨fun n ↦ D.delta (f (n + 1)), by
    intro m n hmn
    apply SModEq.sub_mem.mpr
    have h := (f.property (Nat.add_le_add_right hmn 1))
    have h' : f (m + 1) - f (n + 1) ∈ I ^ (m + 1) := by
      simpa [SModEq.sub_mem, smul_eq_mul] using h
    simpa [smul_eq_mul] using D.delta_sub_mem_pow I hp m _ _ h'⟩

/-- 古典的完備化の元を表すCauchy列にδを作用させる。
以下の座標式により選択した代表列によらない。 -/
def adicDeltaExtension (D : DeltaStructure p R) (I : Ideal R) (hp : (p : R) ∈ I)
    (x : AdicCompletion I R) : AdicCompletion I R :=
  AdicCompletion.mk I R
    (D.adicDeltaSequence I hp (Classical.choose (AdicCompletion.mk_surjective I R x)))

/-- 延長写像のn番目の座標は、元のn+1番目の座標に降下δを適用したもの。 -/
theorem eval_adicDeltaExtension (D : DeltaStructure p R) (I : Ideal R)
    (hp : (p : R) ∈ I) (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ I n (D.adicDeltaExtension I hp x) =
      D.adicDeltaStep I n (AdicCompletion.evalₐ I (n + 1) x) := by
  let f := Classical.choose (AdicCompletion.mk_surjective I R x)
  have hf : AdicCompletion.mk I R f = x :=
    Classical.choose_spec (AdicCompletion.mk_surjective I R x)
  change AdicCompletion.evalₐ I n (AdicCompletion.mk I R (D.adicDeltaSequence I hp f)) = _
  rw [AdicCompletion.evalₐ_mk, ← hf, AdicCompletion.evalₐ_mk, D.adicDeltaStep_mk I hp]
  rfl

/-- 基底のδ写像を標準完備化射で延長する。 -/
@[simp] theorem adicDeltaExtension_of (D : DeltaStructure p R) (I : Ideal R)
    (hp : (p : R) ∈ I) (x : R) :
    D.adicDeltaExtension I hp (AdicCompletion.of I R x) =
      AdicCompletion.of I R (D.delta x) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [D.eval_adicDeltaExtension, AdicCompletion.evalₐ_of, D.adicDeltaStep_mk I hp,
    AdicCompletion.evalₐ_of]

/-- 任意の代表Cauchy列についてδ延長の値が一段ずらしたδ列に一致する。
代表列の選択に依存しないことの具体的な証明。 -/
theorem adicDeltaExtension_mk (D : DeltaStructure p R) (I : Ideal R)
    (hp : (p : R) ∈ I) (f : AdicCauchySequence I R) :
    D.adicDeltaExtension I hp (AdicCompletion.mk I R f) =
      AdicCompletion.mk I R (D.adicDeltaSequence I hp f) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [D.eval_adicDeltaExtension, AdicCompletion.evalₐ_mk, D.adicDeltaStep_mk I hp,
    AdicCompletion.evalₐ_mk]
  rfl

end SerrePositivity.BhattScholze.DeltaStructure
