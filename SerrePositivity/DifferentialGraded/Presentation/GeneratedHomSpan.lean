module
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHomWords
public import Mathlib.LinearAlgebra.Span.Defs
/-!
概要：指定係数の有限語の線形 span は、単位・微分・合成で閉じた斉次 Hom 族を与える。
方針：語の構成子と span の一変数・二変数帰納法を使い、dg 関手像も照合する。
規約：生成係数をラベルで保持し、任意の閉射がこの span に入るとは仮定なく主張しない。
使われ方：c′ の dg 係数閉包と固定基底 Hom 提示への再符号化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {I J : Type u} (source target : I → J) (degree : I → ℤ)
  (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] (value : J → D)
  (coefficient : ∀ i, GradedHom R (value (source i)) (value (target i)) (degree i))

namespace DGGeneratedHomWord

def linearSpan (x y : J) (n : ℤ) : Submodule R (GradedHom R (value x) (value y) n) :=
  Submodule.span R (Set.range (evaluate source target degree R D value coefficient
    (x := x) (y := y) (n := n)))

lemma evaluate_mem_span {x y : J} {n : ℤ}
    (a : DGGeneratedHomWord source target degree x y n) :
    evaluate source target degree R D value coefficient a ∈
      linearSpan source target degree R D value coefficient x y n :=
  Submodule.subset_span ⟨a, rfl⟩

lemma differential_mem_span {x y : J} {n : ℤ} {f : GradedHom R (value x) (value y) n}
    (hf : f ∈ linearSpan source target degree R D value coefficient x y n) :
    differential R f ∈ linearSpan source target degree R D value coefficient x y (n + 1) := by
  induction hf using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, rfl⟩ := hz
    exact evaluate_mem_span source target degree R D value coefficient (.derivative a)
  | zero => simpa only [differential, map_zero] using
      (linearSpan source target degree R D value coefficient x y (n + 1)).zero_mem
  | add f g _ _ hf hg =>
    simpa only [differential, map_add] using
      (linearSpan source target degree R D value coefficient x y (n + 1)).add_mem hf hg
  | smul a f _ hf =>
    simpa only [differential, map_smul] using
      (linearSpan source target degree R D value coefficient x y (n + 1)).smul_mem a hf

lemma forward_mem_span {x y z : J} {p q : ℤ}
    {f : GradedHom R (value x) (value y) p} {g : GradedHom R (value y) (value z) q}
    (hf : f ∈ linearSpan source target degree R D value coefficient x y p)
    (hg : g ∈ linearSpan source target degree R D value coefficient y z q) :
    forward R f g rfl ∈ linearSpan source target degree R D value coefficient x z (p + q) := by
  let S := linearSpan source target degree R D value coefficient x z (p + q)
  refine Submodule.span_induction₂ (p := fun f g _ _ => forward R f g rfl ∈ S)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hf hg
  · intro f g hf hg
    obtain ⟨a, rfl⟩ := hf
    obtain ⟨b, rfl⟩ := hg
    exact evaluate_mem_span source target degree R D value coefficient (.composition a b)
  · intro g _
    simpa [forward] using S.zero_mem
  · intro f _
    simpa [forward] using S.zero_mem
  · intro f f' g _ _ _ hf hf'
    simpa [forward, TensorProduct.add_tmul, map_add] using S.add_mem hf hf'
  · intro f g g' _ _ _ hg hg'
    simpa [forward, TensorProduct.tmul_add, map_add] using S.add_mem hg hg'
  · intro a f g _ _ hf
    simpa [forward, TensorProduct.smul_tmul, map_smul] using S.smul_mem a hf
  · intro a f g _ _ hg
    simpa [forward, TensorProduct.tmul_smul, map_smul] using S.smul_mem a hg

variable (E : Type w) [DGCategory R E] (F : DGFunctor R D E)

lemma map_mem_span {x y : J} {n : ℤ} {f : GradedHom R (value x) (value y) n}
    (hf : f ∈ linearSpan source target degree R D value coefficient x y n) :
    (F.map (value x) (value y)).f n f ∈
      linearSpan source target degree R E (F.obj ∘ value)
        (fun i => (F.map (value (source i)) (value (target i))).f (degree i) (coefficient i)) x y n := by
  let S := linearSpan source target degree R E (F.obj ∘ value)
    (fun i => (F.map (value (source i)) (value (target i))).f (degree i) (coefficient i)) x y n
  induction hf using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, rfl⟩ := hz
    rw [evaluate_map]
    exact evaluate_mem_span source target degree R E _ _ a
  | zero => simpa only [map_zero] using S.zero_mem
  | add f g _ _ hf hg => simpa only [map_add] using S.add_mem hf hg
  | smul a f _ hf => simpa only [map_smul] using S.smul_mem a hf

end DGGeneratedHomWord
end SerrePositivity.DifferentialGraded
