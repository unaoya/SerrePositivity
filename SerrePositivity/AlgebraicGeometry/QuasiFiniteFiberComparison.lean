module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
概要：基底の一点上で準有限となる写像から、元の写像の点での準有限性を得る。
方針：ファイバーの離散性を周辺スキームへの埋め込みで移す。
規約：元のファイバー全体が周辺スキームへの埋め込みの像に入ると仮定する。
使われ方：多項式写像の剰余体への基底変更の有限性から、Zariski の主定理の入力を得る。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Topology

/--
概要：準有限な写像の一つのファイバーが埋め込みで元のファイバー全体を覆えば、元の写像はその点で準有限。
方針：可換四角形と下側の点への単射性でファイバーの像を計算する。
規約：埋め込みには開埋め込み性を要求しない。
使われ方：アフィンファイバー上の有限な Noether 正規化から点での準有限性を導く。
-/
theorem quasiFiniteAt_of_fiber_subset_range
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (i : X' ⟶ X) [IsPreimmersion i] (j : Y' ⟶ Y) [IsPreimmersion j]
    (g : X' ⟶ Y') [LocallyQuasiFinite g] (hcomm : i ≫ f = g ≫ j)
    {x : X} (y' : Y') (hy : j y' = f x) (hsub : f ⁻¹' {f x} ⊆ Set.range i) :
    f.QuasiFiniteAt x := by
  have he (z : X') : f (i z) = j (g z) := congrArg (fun k : X' ⟶ Y => k z) hcomm
  have hset : i '' (g ⁻¹' {y'}) = f ⁻¹' {f x} := by
    ext z
    constructor
    · rintro ⟨z', hz', rfl⟩
      change f (i z') = f x
      change g z' = y' at hz'
      rw [he, hz', hy]
    · intro hz
      obtain ⟨z', rfl⟩ := hsub hz
      refine ⟨z', ?_, rfl⟩
      change g z' = y'
      exact j.isEmbedding.injective ((he z').symm.trans (hz.trans hy.symm))
  have hd : _root_.IsDiscrete (f ⁻¹' {f x}) :=
    hset ▸ (g.isDiscrete_preimage_singleton y').image i.isEmbedding.isInducing
  let : DiscreteTopology (f ⁻¹' {f x} : Set X) := isDiscrete_iff_discreteTopology.mp hd
  let : DiscreteTopology (f.fiber (f x)) := (f.fiberHomeo (f x)).isEmbedding.discreteTopology
  exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)

end SerrePositivity.AlgebraicGeometry
