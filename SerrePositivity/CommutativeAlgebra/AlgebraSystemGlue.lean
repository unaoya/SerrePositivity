module

public import SerrePositivity.CommutativeAlgebra.AlgebraSystemReindex

/-! # 一致する初期部分の図式の貼り合わせ

段の環S_iを共有し、制限が一致する閉初期部分の図式から、全体の遷移写像を定義する。
各写像を終域の添字までの図式から取り出し、局所の自己・合成則を全体へ移す。
これは段の環と初期部分の整合性を構成する再帰そのものではない。
-/

@[expose] public section
namespace SerrePositivity
variable {B ι : Type*} [CommRing B] [Preorder ι]
variable (S : ι → Type*) [∀ i, CommRing (S i)] [∀ i, Algebra B (S i)]
variable (p : ∀ l, ∀ j k : {j : ι // j ≤ l}, j ≤ k → S j.val →ₐ[B] S k.val)
variable (hp : ∀ i l (hil : i ≤ l) (j k : {j : ι // j ≤ i}) (h : j ≤ k),
  p i j k h = p l ⟨j.val, j.property.trans hil⟩ ⟨k.val, k.property.trans hil⟩ h)

/-- 遷移写像を、終域の添字までの図式から取り出す。 -/
def algebraSystemGlueMap : ∀ j k, j ≤ k → S j →ₐ[B] S k :=
  fun j k h ↦ p k ⟨j, h⟩ ⟨k, le_rfl⟩ h

include hp in
/-- 貼り合わせた写像を任意の初期部分へ制限すると、元の写像に一致する。 -/
theorem algebraSystemGlueMap_restrict (l j k : ι) (hj : j ≤ l) (hk : k ≤ l) (h : j ≤ k) :
    algebraSystemGlueMap S p j k h = p l ⟨j, hj⟩ ⟨k, hk⟩ h :=
  hp k l hk ⟨j, h⟩ ⟨k, le_rfl⟩ h

include hp in
/-- 各初期部分の図式が有向図式の法則を満たせば、貼り合わせた全体も満たす。 -/
theorem algebraSystemGlue_directedSystem
    [∀ l, DirectedSystem (fun j : {j : ι // j ≤ l} ↦ S j.val) (p l · · ·)] :
    DirectedSystem S (algebraSystemGlueMap S p · · ·) := by
  constructor
  · intro j x
    exact DirectedSystem.map_self' (f := p j) (i := ⟨j, le_rfl⟩) x
  · intro k j i hij hjk x
    rw [algebraSystemGlueMap_restrict S p hp k j k hjk le_rfl hjk,
      algebraSystemGlueMap_restrict S p hp k i j (hij.trans hjk) hjk hij,
      algebraSystemGlueMap_restrict S p hp k i k (hij.trans hjk) le_rfl (hij.trans hjk)]
    exact DirectedSystem.map_map' (f := p k) (i := ⟨i, hij.trans hjk⟩)
      (j := ⟨j, hjk⟩) (k := ⟨k, le_rfl⟩) hij hjk x

/-- 各初期部分の遷移が局所なら、全体の遷移も局所である。 -/
theorem algebraSystemGlue_isLocalHom
    (hlocal : ∀ l j k h, IsLocalHom (p l j k h).toRingHom) :
    ∀ j k h, IsLocalHom (algebraSystemGlueMap S p j k h).toRingHom :=
  fun j k h ↦ hlocal k ⟨j, h⟩ ⟨k, le_rfl⟩ h

section Target
variable {K : Type*} [CommRing K] [Algebra B K]
variable (g : ∀ j, S j →ₐ[B] K)

/-- 指定終域への両立は、各初期部分での両立から従う。 -/
theorem algebraSystemGlueTarget_compatible
    (hg : ∀ l j k h x, g k.val (p l j k h x) = g j.val x) :
    ∀ j k h x, g k (algebraSystemGlueMap S p j k h x) = g j x :=
  fun j k h x ↦ hg k ⟨j, h⟩ ⟨k, le_rfl⟩ h x

end Target
end SerrePositivity
