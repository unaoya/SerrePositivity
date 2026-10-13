module

public import SerrePositivity.CommutativeAlgebra.ResidueFieldBeforeExtension
public import SerrePositivity.CommutativeAlgebra.ResidueFieldMinExtension

/-! # 空・非空を統合した閉初期部分の延長

最小元では基底環から、それ以外では開初期部分の直極限から一元を加える。
実際の環と写像を構成する存在定理の後に、検証済み候補を選ぶ関数を置く。
全段で一致する履歴の再帰構成は、この一段延長とは別に証明する必要がある。
-/

@[expose] public section
namespace SerrePositivity
open IsLocalRing
universe u
variable {B K : Type u} [CommRing B] [IsLocalRing B] [Field K]
variable [Algebra (ResidueField B) K] [Algebra B K] [IsScalarTower B (ResidueField B) K]
variable [LinearOrder K]

/-- 開初期部分の空・非空にかかわらず、同じ法則を満たす閉延長を構成する。 -/
theorem exists_residueField_closed_extension
    (i : K) (S : {j : K // j < i} → Type u)
    [∀ j, CommRing (S j)] [∀ j, IsLocalRing (S j)] [∀ j, Algebra B (S j)]
    [∀ j, IsLocalHom (algebraMap B (S j))] [∀ j, Module.Flat B (S j)]
    (f : ∀ j k, j ≤ k → S j →ₐ[B] S k) [DirectedSystem S (f · · ·)]
    (g : ∀ j, S j →ₐ[B] K)
    (hrange : ∀ j, Set.range (g j) = (residueGeneratorAfter (ResidueField B) K j.val : Set K))
    (hg : ∀ j k h x, g k (f j k h x) = g j x)
    (hlocal : ∀ j k h, IsLocalHom (f j k h).toRingHom)
    (hmax : ∀ j, (maximalIdeal B).map (algebraMap B (S j)) = maximalIdeal (S j)) :
    ∃ (T : Type u) (_ : CommRing T) (_ : IsLocalRing T) (_ : Algebra B T)
      (_ : IsLocalHom (algebraMap B T)),
      ∃ (c : ∀ j, S j →ₐ[B] T) (gT : T →ₐ[B] K),
        IsResidueFieldClosedExtension i S f g T c gT := by
  classical
  by_cases h : Nonempty {j : K // j < i}
  · let := h
    obtain ⟨T, tRing, tLocal, tAlg, tHom, c, gT,
      hflat, htmax, htrange, htker, htgen, hc, hgc, hds, hclosedLocal,
      htarget, hclosedFlat, hclosedMax, hclosedRange⟩ :=
      exists_closed_extension_of_beforeLimit i S f g hrange hg hlocal hmax
    have hcLocal (j : {j : K // j < i}) : IsLocalHom (c j).toRingHom := by
      apply ((local_hom_TFAE (c j).toRingHom).out 1 3).mpr
      rw [← hmax j, Ideal.map_map]
      have hcomp : (c j).toRingHom.comp (algebraMap B (S j)) = algebraMap B T := by
        ext b
        exact (c j).commutes b
      rw [hcomp, htmax]
    exact ⟨T, tRing, tLocal, tAlg, tHom, c, gT,
      hflat, htmax, htrange, htker, htgen, hc, hgc, hcLocal,
      hds, hclosedLocal, htarget, hclosedFlat, hclosedMax, hclosedRange⟩
  · have hi : IsMin i := by
      refine isMin_iff_forall_not_lt.mpr ?_
      intro j hj
      exact h ⟨⟨j, hj⟩⟩
    exact exists_closed_extension_of_min i hi S f g

/-- 延長の対象と写像。平坦性・像・図式の両立は別の述語で検証する。 -/
structure ResidueFieldClosedStepData
    (i : K) (S : {j : K // j < i} → Type u)
    [∀ j, CommRing (S j)] [∀ j, Algebra B (S j)] where
  carrier : Type u
  [commRing : CommRing carrier]
  [localRing : IsLocalRing carrier]
  [algebra : Algebra B carrier]
  [baseLocal : IsLocalHom (algebraMap B carrier)]
  incoming : ∀ j, S j →ₐ[B] carrier
  target : carrier →ₐ[B] K

attribute [instance] ResidueFieldClosedStepData.commRing ResidueFieldClosedStepData.localRing
  ResidueFieldClosedStepData.algebra ResidueFieldClosedStepData.baseLocal

variable (i : K) (S : {j : K // j < i} → Type u)
variable [∀ j, CommRing (S j)] [∀ j, IsLocalRing (S j)] [∀ j, Algebra B (S j)]
variable [∀ j, IsLocalHom (algebraMap B (S j))] [∀ j, Module.Flat B (S j)]
variable (f : ∀ j k, j ≤ k → S j →ₐ[B] S k) [DirectedSystem S (f · · ·)]
variable (g : ∀ j, S j →ₐ[B] K)
variable (hrange : ∀ j, Set.range (g j) = (residueGeneratorAfter (ResidueField B) K j.val : Set K))
variable (hg : ∀ j k h x, g k (f j k h x) = g j x)
variable (hlocal : ∀ j k h, IsLocalHom (f j k h).toRingHom)
variable (hmax : ∀ j, (maximalIdeal B).map (algebraMap B (S j)) = maximalIdeal (S j))

include hrange hg hlocal hmax

/-- 候補の存在と検証を、対象を格納する型に移す。 -/
theorem exists_lawful_residueFieldClosedStepData :
    ∃ d : ResidueFieldClosedStepData (B := B) i S,
      IsResidueFieldClosedExtension i S f g d.carrier d.incoming d.target := by
  obtain ⟨T, tRing, tLocal, tAlg, tHom, c, gT, h⟩ :=
    exists_residueField_closed_extension i S f g hrange hg hlocal hmax
  exact ⟨{
    carrier := T
    commRing := tRing
    localRing := tLocal
    algebra := tAlg
    baseLocal := tHom
    incoming := c
    target := gT }, h⟩

/-- 同じ入力には同じ候補を返す一段延長。法則は下の定理で保証する。 -/
noncomputable def residueFieldClosedStep : ResidueFieldClosedStepData (B := B) i S :=
  Classical.choose (exists_lawful_residueFieldClosedStepData i S f g hrange hg hlocal hmax)

/-- 選んだ対象と写像は、構成した閉延長の全法則を満たす。 -/
theorem residueFieldClosedStep_spec :
    let d := residueFieldClosedStep i S f g hrange hg hlocal hmax
    IsResidueFieldClosedExtension i S f g d.carrier d.incoming d.target :=
  Classical.choose_spec (exists_lawful_residueFieldClosedStepData i S f g hrange hg hlocal hmax)

end SerrePositivity
