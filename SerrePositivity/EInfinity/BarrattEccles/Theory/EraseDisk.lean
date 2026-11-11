module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.EraseDifferential
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# セル付加の disk の次数付き分解

## 概要
Berger–Moerdijk 命題 4.1 の生成余ファイブレーションに現れる disk を、
微分を消して境界と新生成元の余積に分解する。

## 方針
次数ごとの既存の disk 分裂を、零微分の複体の射にする。

## 規約
余鎖次数 n の生成元と次数 n + 1 の境界を取る。

## 使われ方
セル付加の pushout を次数付き代数の余積に変える。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory Limits DifferentialGraded CochainComplex HomComplex

variable (A : Type u) [CommRing A]

/-- A degree-zero cochain becomes a map after erasing both differentials. -/
def eraseDifferentialMapOfCochain {K L : Complex A} (f : Cochain K L 0) :
    (eraseDifferential A).obj K ⟶ (eraseDifferential A).obj L where
  f i := f.v i i (add_zero i)
  comm' := by
    intro i j h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change 0 = (f.v j j (add_zero j)).hom 0
    exact (map_zero _).symm

/-- The sphere inclusion splits, with the new generator as its complement. -/
def erasedDiskSphereSplitting (n : ℤ) :
    ((complexDiskSphereShortComplex A n).map (eraseDifferential A)).Splitting where
  r := eraseDifferentialMapOfCochain A (complexDiskGradedRetraction A n)
  s := eraseDifferentialMapOfCochain A (complexDiskGradedSection A n)
  f_r := by
    apply HomologicalComplex.Hom.ext
    funext i
    exact complexDiskGraded_inclusion_retraction A n i
  s_g := by
    apply HomologicalComplex.Hom.ext
    funext i
    exact complexDiskGraded_section_projection A n i
  id := by
    apply HomologicalComplex.Hom.ext
    funext i
    exact complexDiskGraded_decomposition A n i

/-- The boundary and the new generator exhibit the erased disk as a coproduct. -/
def erasedDiskCofanIsColimit (n : ℤ) :
    IsColimit (BinaryCofan.mk ((eraseDifferential A).map (complexSphereToDisk A n))
      (erasedDiskSphereSplitting A n).s) := by
  let S := (complexDiskSphereShortComplex A n).map (eraseDifferential A)
  let h := erasedDiskSphereSplitting A n
  have hs : h.s ≫ h.r = 0 := by
    apply HomologicalComplex.Hom.ext
    funext i
    exact complexDiskGraded_section_retraction A n i
  change IsColimit (BinaryCofan.mk S.f h.s)
  refine BinaryCofan.IsColimit.mk _ (fun f g => h.r ≫ f + S.g ≫ g) ?_ ?_ ?_
  · intro W f g
    change S.f ≫ (h.r ≫ f + S.g ≫ g) = f
    simp only [Preadditive.comp_add, S.zero_assoc, zero_comp, add_zero]
    exact h.f_r_assoc f
  · intro W f g
    change h.s ≫ (h.r ≫ f + S.g ≫ g) = g
    simp only [Preadditive.comp_add, reassoc_of% hs, zero_comp, zero_add]
    exact h.s_g_assoc g
  · intro W f g m hf hg
    change S.f ≫ m = f at hf
    change h.s ≫ m = g at hg
    symm
    rw [← hf, ← hg, ← Category.assoc, ← Category.assoc, ← Preadditive.add_comp,
      h.id, Category.id_comp]

/-- The erased disk is the binary biproduct of its boundary and the sphere of its generator. -/
def erasedDiskBiproductIso (n : ℤ) :
    (eraseDifferential A).obj (complexDisk A n) ≅
      (eraseDifferential A).obj (complexSphere A (n + 1)) ⊞
        (eraseDifferential A).obj (complexSphere A n) :=
  (erasedDiskSphereSplitting A n).isoBinaryBiproduct

end SerrePositivity.EInfinity
