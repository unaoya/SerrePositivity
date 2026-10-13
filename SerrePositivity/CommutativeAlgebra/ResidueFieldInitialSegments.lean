module

public import SerrePositivity.CommutativeAlgebra.AlgebraSystemGlue
public import SerrePositivity.CommutativeAlgebra.ResidueFieldDirectLimit

/-! # 初期部分の図式から剰余体拡大の極限へ

構成済みの初期部分の図式の制限一致から全体の遷移写像を作り、
局所性・平坦性・剰余体同型の保存定理を実際に適用する。
初期部分の環と整合性を選ぶ全段の依存再帰はこの定理の仮定を供給する別の課題。
-/

public section
namespace SerrePositivity
open IsLocalRing
universe u

/-- 両立する初期部分の図式を貼り合わせ、指定体を剰余体に持つ平坦局所拡大を構成する。
全体の遷移写像・有向図式の法則は入力にせず、局所の図式から実際に構成する。 -/
theorem exists_flat_local_extension_of_initialSegments
    {B ι K : Type u} [CommRing B] [IsLocalRing B]
    [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    [Field K] [Algebra (ResidueField B) K] [Algebra B K]
    [IsScalarTower B (ResidueField B) K]
    (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, IsLocalRing (S i)]
    [∀ i, Algebra B (S i)] [∀ i, IsLocalHom (algebraMap B (S i))]
    [∀ i, Module.Flat B (S i)]
    (p : ∀ l, ∀ j k : {j : ι // j ≤ l}, j ≤ k → S j.val →ₐ[B] S k.val)
    [∀ l, DirectedSystem (fun j : {j : ι // j ≤ l} ↦ S j.val) (p l · · ·)]
    (hp : ∀ i l (hil : i ≤ l) (j k : {j : ι // j ≤ i}) (h : j ≤ k),
      p i j k h = p l ⟨j.val, j.property.trans hil⟩ ⟨k.val, k.property.trans hil⟩ h)
    (hlocal : ∀ l j k h, IsLocalHom (p l j k h).toRingHom)
    (hmax : ∀ i, (maximalIdeal B).map (algebraMap B (S i)) = maximalIdeal (S i))
    (g : ∀ i, S i →ₐ[B] K)
    (hg : ∀ l j k h x, g k.val (p l j k h x) = g j.val x)
    (hcover : ∀ x : K, ∃ i, ∃ y : S i, g i y = x) :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsLocalRing C) (_ : Algebra B C)
      (_ : IsLocalHom (algebraMap B C)),
      Module.Flat B C ∧ (maximalIdeal B).map (algebraMap B C) = maximalIdeal C ∧
      ∃ e : ResidueField C ≃+* K,
        ∀ x, e (ResidueField.map (algebraMap B C) x) = algebraMap (ResidueField B) K x := by
  let : DirectedSystem S (algebraSystemGlueMap S p · · ·) :=
    algebraSystemGlue_directedSystem S p hp
  exact exists_flat_local_extension_of_directed_system S (algebraSystemGlueMap S p)
    (algebraSystemGlue_isLocalHom S p hlocal) hmax g
    (algebraSystemGlueTarget_compatible S p g hg) hcover

end SerrePositivity
