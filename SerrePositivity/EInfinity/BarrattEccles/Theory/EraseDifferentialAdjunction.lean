module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.EraseDifferential
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# 微分を消す関手の右随伴

## 概要
Berger–Moerdijk 命題 4.1 のセル付加の次数付き表示に使う余自由複体。

## 方針
次数 i と i+1 の cycle を対にし、第二成分を次の次数の第一成分へ移す。

## 規約
任意の整数次数と任意の可換環を扱う。

## 使われ方
微分を消す操作をオペラッド代数の随伴へ持ち上げる。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory Limits HomologicalComplex DifferentialGraded

variable (A : Type u) [CommRing A]

abbrev cofreeCycleSubmodule (K : Complex A) (i : ℤ) :=
  LinearMap.ker (K.d i (i + 1)).hom

def cofreeCycleMap {K L : Complex A} (f : K ⟶ L) (i : ℤ) :
    cofreeCycleSubmodule A K i →ₗ[A] cofreeCycleSubmodule A L i :=
  (f.f i).hom.restrict (p := cofreeCycleSubmodule A K i) (q := cofreeCycleSubmodule A L i) (by
    intro x hx
    change L.d i (i + 1) (f.f i x) = 0
    have h := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (f.comm i (i + 1))) x
    change L.d i (i + 1) (f.f i x) = f.f (i + 1) (K.d i (i + 1) x) at h
    rw [h, show K.d i (i + 1) x = 0 from hx, map_zero])

def cofreeCyclesD (K : Complex A) (i : ℤ) :
    ModuleCat.of A (cofreeCycleSubmodule A K i × cofreeCycleSubmodule A K (i + 1)) ⟶
      ModuleCat.of A (cofreeCycleSubmodule A K (i + 1) × cofreeCycleSubmodule A K (i + 1 + 1)) :=
  ModuleCat.ofHom ((LinearMap.snd A _ _).prod 0)

/-- The cofree complex on the cycles of a complex. -/
def cofreeCycles : Complex A ⥤ Complex A where
  obj K := CochainComplex.of
    (fun i => ModuleCat.of A (cofreeCycleSubmodule A K i × cofreeCycleSubmodule A K (i + 1)))
    (cofreeCyclesD A K) (by
      intro i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact Prod.ext rfl rfl)
  map f :=
    { f := fun i => ModuleCat.ofHom ((cofreeCycleMap A f i).prodMap (cofreeCycleMap A f (i + 1)))
      comm' := by
        intro i j h
        change i + 1 = j at h
        subst j
        simp only [CochainComplex.of_d]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact Prod.ext rfl (by simp [cofreeCyclesD]) }
  map_id K := by
    apply HomologicalComplex.Hom.ext
    funext i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)

def eraseMapToCycles {X Y : Complex A} (f : (eraseDifferential A).obj X ⟶ Y) (i : ℤ) :
    X.X i →ₗ[A] cofreeCycleSubmodule A Y i :=
  LinearMap.codRestrict _ (f.f i).hom (by
    intro x
    change Y.d i (i + 1) (f.f i x) = 0
    have h := f.comm i (i + 1)
    rw [eraseDifferential_d, zero_comp] at h
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) x)

def transposeToCofree {X Y : Complex A} (f : (eraseDifferential A).obj X ⟶ Y) :
    X ⟶ (cofreeCycles A).obj Y where
  f i := ModuleCat.ofHom ((eraseMapToCycles A f i).prod
    ((eraseMapToCycles A f (i + 1)).comp (X.d i (i + 1)).hom))
  comm' := by
    intro i j h
    change i + 1 = j at h
    subst j
    simp only [cofreeCycles, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · rfl
    apply Subtype.ext
    change 0 = f.f (i + 1 + 1) (X.d (i + 1) (i + 1 + 1) (X.d i (i + 1) x))
    have h := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (X.d_comp_d i (i + 1)
      (i + 1 + 1))) x
    change X.d (i + 1) (i + 1 + 1) (X.d i (i + 1) x) = 0 at h
    rw [h]
    exact (f.f (i + 1 + 1)).hom.map_zero.symm

def transposeFromCofree {X Y : Complex A} (g : X ⟶ (cofreeCycles A).obj Y) :
    (eraseDifferential A).obj X ⟶ Y where
  f i := ModuleCat.ofHom ((cofreeCycleSubmodule A Y i).subtype.comp
    ((LinearMap.fst A _ _).comp (g.f i).hom))
  comm' := by
    intro i j h
    change i + 1 = j at h
    subst j
    erw [eraseDifferential_d, zero_comp]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change Y.d i (i + 1) (g.f i x).1.val = 0
    exact (g.f i x).1.property

/-- Erasing the differential is left adjoint to the cofree complex on cycles. -/
def eraseDifferentialAdjunction : eraseDifferential A ⊣ cofreeCycles A :=
  Adjunction.mkOfHomEquiv
    { homEquiv X Y :=
        { toFun := transposeToCofree A
          invFun := transposeFromCofree A
          left_inv f := by
            apply HomologicalComplex.Hom.ext
            funext i
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro x
            rfl
          right_inv g := by
            apply HomologicalComplex.Hom.ext
            funext i
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro x
            apply Prod.ext
            · rfl
            have hc := g.comm i (i + 1)
            simp only [cofreeCycles, CochainComplex.of_d] at hc
            have h := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hc) x
            change (g.f (i + 1) (X.d i (i + 1) x)).1 = (g.f i x).2
            have h' := congrArg Prod.fst h
            change (g.f i x).2 = (g.f (i + 1) (X.d i (i + 1) x)).1 at h'
            exact h'.symm }
      homEquiv_naturality_left_symm f g := by
        apply HomologicalComplex.Hom.ext
        funext i
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        rfl
      homEquiv_naturality_right f g := by
        change transposeToCofree A (f ≫ g) = transposeToCofree A f ≫ (cofreeCycles A).map g
        apply HomologicalComplex.Hom.ext
        funext i
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact Prod.ext (Subtype.ext rfl) (Subtype.ext rfl) }

end SerrePositivity.EInfinity
