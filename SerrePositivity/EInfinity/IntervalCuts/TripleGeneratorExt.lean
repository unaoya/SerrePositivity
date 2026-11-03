module

public import SerrePositivity.EInfinity.IntervalCuts.GeneratorLinearExt
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying

/-!
# 語基底と区間三生成元による全整数三重テンソル射の外延性

概要：Berger–Fresse §2.2.6・§3.1 の生成元比較を実際の非有界複体射の等式へ移す。
方針：三重斉次外延性、正次数の零性、二つの語基底と区間生成元の線形外延性を使う。
規約：モデル構造の仮定を持たず、arity 零も含む。
使われ方：具体的な区間余作用の部分合成則を複体射として閉じる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.IntervalCuts

open CategoryTheory MonoidalCategory HomologicalComplex Surjection
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：二語の基底係数と頂点による実際の三重斉次入力（BF §3.1）。
方針：内外語の負次数を標準包含で合わせ、区間頂点を最後に置く。
規約：係数の順序は外側・内側、頂点次数は零。
使われ方：複体射の部分合成則の頂点生成元と外延性。 -/
def wordPairVertexInput {m n d e : ℕ} (v : BasisWord m d) (w : BasisWord n e) (b : Fin 2) :
    ((complex A m ⊗ complex A n) ⊗ interval A).X (-((d + e : ℕ) : ℤ)) :=
  ιTensorObj (complex A m ⊗ complex A n) (interval A) (-((d + e : ℕ) : ℤ)) 0
    (-((d + e : ℕ) : ℤ)) (by omega)
    (ιTensorObj (complex A m) (complex A n) (-(d : ℤ)) (-(e : ℤ))
      (-((d + e : ℕ) : ℤ)) (by omega)
      ((complexXIso A m d).inv (basis A m d (ULift.up v)) ⊗ₜ[A]
        (complexXIso A n e).inv (basis A n e (ULift.up w))) ⊗ₜ[A] faceVector A (vertex b))

/-- 概要：二語の基底係数と辺による実際の三重斉次入力（BF §3.1）。
方針：内外語の負次数を合わせ、区間の次数 −1 の辺を最後に置く。
規約：全次数は −(d+e+1)。
使われ方：複体射の部分合成則の辺生成元と外延性。 -/
def wordPairEdgeInput {m n d e : ℕ} (v : BasisWord m d) (w : BasisWord n e) :
    ((complex A m ⊗ complex A n) ⊗ interval A).X (-((d + e + 1 : ℕ) : ℤ)) :=
  ιTensorObj (complex A m ⊗ complex A n) (interval A) (-((d + e : ℕ) : ℤ)) (-1)
    (-((d + e + 1 : ℕ) : ℤ)) (by omega)
    (ιTensorObj (complex A m) (complex A n) (-(d : ℤ)) (-(e : ℤ))
      (-((d + e : ℕ) : ℤ)) (by omega)
      ((complexXIso A m d).inv (basis A m d (ULift.up v)) ⊗ₜ[A]
        (complexXIso A n e).inv (basis A n e (ULift.up w))) ⊗ₜ[A] faceVector A edge)

/-- 概要：二つの χ 係数と区間からの複体射は語基底と三生成元で決まる（BF §3.1）。
方針：全整数三重斉次成分を非正二次数と区間二次数へ制限し、各基底で比較する。
規約：標的複体と二 arity は任意。
使われ方：生成元での実際の部分合成則を全複体射の等式へ延長する。 -/
lemma coefficient_interval_hom_ext (m n : ℕ) {K : Complex A}
    {f g : (complex A m ⊗ complex A n) ⊗ interval A ⟶ K}
    (hv : ∀ (d e : ℕ) (v : BasisWord m d) (w : BasisWord n e) (b : Fin 2),
      f.f (-((d + e : ℕ) : ℤ)) (wordPairVertexInput A v w b) =
        g.f (-((d + e : ℕ) : ℤ)) (wordPairVertexInput A v w b))
    (he : ∀ (d e : ℕ) (v : BasisWord m d) (w : BasisWord n e),
      f.f (-((d + e + 1 : ℕ) : ℤ)) (wordPairEdgeInput A v w) =
        g.f (-((d + e + 1 : ℕ) : ℤ)) (wordPairEdgeInput A v w)) : f = g := by
  apply triple_ext
  intro r s t z hz
  by_cases hr : 0 < r
  · apply ModuleCat.hom_ext
    apply TensorProduct.ext_threefold
    intro x y w
    simp only [complex_eq_zero_of_positive A m r hr x, TensorProduct.zero_tmul, map_zero]
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, r = -(d : ℤ) := ⟨(-r).toNat, by omega⟩
  by_cases hs : 0 < s
  · apply ModuleCat.hom_ext
    apply TensorProduct.ext_threefold
    intro x y w
    simp only [complex_eq_zero_of_positive A n s hs y, TensorProduct.tmul_zero,
      TensorProduct.zero_tmul, map_zero]
  obtain ⟨e, rfl⟩ : ∃ e : ℕ, s = -(e : ℤ) := ⟨(-s).toNat, by omega⟩
  by_cases ht : t = 0
  · subst t
    have hz' : z = -((d + e : ℕ) : ℤ) := by omega
    cases hz'
    apply ModuleCat.hom_ext
    apply coefficient_vertex_linear_ext A m n d e
    intro v w b
    have hx := SerrePositivity.DifferentialGraded.nested_left_apply
      (complex A m) (complex A n) (interval A) (-(d : ℤ)) (-(e : ℤ)) 0
      (-((d + e : ℕ) : ℤ)) (-((d + e : ℕ) : ℤ)) (by omega) (by omega)
      ((complexXIso A m d).inv (basis A m d (ULift.up v)))
      ((complexXIso A n e).inv (basis A n e (ULift.up w))) (faceVector A (vertex b))
    exact (congrArg (fun x => f.f (-((d + e : ℕ) : ℤ)) x) hx).symm.trans
      ((hv d e v w b).trans (congrArg (fun x => g.f (-((d + e : ℕ) : ℤ)) x) hx))
  by_cases ht1 : t = -1
  · subst t
    have hz' : z = -((d + e + 1 : ℕ) : ℤ) := by omega
    cases hz'
    apply ModuleCat.hom_ext
    apply coefficient_edge_linear_ext A m n d e
    intro v w
    have hx := SerrePositivity.DifferentialGraded.nested_left_apply
      (complex A m) (complex A n) (interval A) (-(d : ℤ)) (-(e : ℤ)) (-1)
      (-((d + e : ℕ) : ℤ)) (-((d + e + 1 : ℕ) : ℤ)) (by omega) (by omega)
      ((complexXIso A m d).inv (basis A m d (ULift.up v)))
      ((complexXIso A n e).inv (basis A n e (ULift.up w))) (faceVector A edge)
    exact (congrArg (fun x => f.f (-((d + e + 1 : ℕ) : ℤ)) x) hx).symm.trans
      ((he d e v w).trans (congrArg (fun x => g.f (-((d + e + 1 : ℕ) : ℤ)) x) hx))
  · apply ModuleCat.hom_ext
    apply TensorProduct.ext_threefold
    intro x y w
    simp only [interval_eq_zero_of_other A t ht ht1 w, TensorProduct.tmul_zero, map_zero]

end SerrePositivity.EInfinity.IntervalCuts
