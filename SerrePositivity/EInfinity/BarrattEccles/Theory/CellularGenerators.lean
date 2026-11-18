module

public import SerrePositivity.EInfinity.BarrattEccles.ModelCategory
public import SerrePositivity.DifferentialGraded.Module.Disk
public import Mathlib.AlgebraicTopology.RelativeCellComplex.AttachCells

/-!
# 付加セルの生成元と微分

## 概要
Berger–Moerdijk 命題 4.1 の生成余ファイブレーションによる付加で、生成元と境界を取り出す。

## 方針
自由代数随伴を sphere と disk に適用し、付加の pushout の可換性を使う。

## 規約
境界は余鎖次数 n + 1 の cycle として取る。

## 使われ方
セル代数の準自由表示で、付加セルの微分を先行段の元として記述する。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

namespace SerrePositivity.EInfinity.Operad

open CategoryTheory Limits HomotopicalAlgebra
open DifferentialGraded

variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A} {X Y : P.Algebra} {g : X ⟶ Y}
  (c : AttachCells.{w} (fun n => P.freeAlgebraFunctor.map (complexSphereToDisk A n)) g)

/-- 付加された disk の下の生成元の像。 -/
def attachedGenerator (i : c.ι) : Y.carrier.X (c.π i) :=
  complexDiskHomEquiv A Y.carrier (c.π i)
    (P.freeAlgebraAdjunction.homEquiv _ _ (c.cell i))

/-- 付加の境界射が先行段で指定する cycle。 -/
def attachedBoundary (i : c.ι) : complexCycles A X.carrier (c.π i + 1) :=
  complexSphereHomEquiv A X.carrier (c.π i + 1)
    (P.freeAlgebraAdjunction.homEquiv _ _ (c.cofan₁.inj i ≫ c.g₁))

/-- 新しい生成元の微分は、付加の境界 cycle の像に一致する。 -/
lemma attachedGenerator_d (i : c.ι) :
    Y.carrier.d (c.π i) (c.π i + 1) (attachedGenerator c i) =
      g.hom.f (c.π i + 1) (attachedBoundary c i).val := by
  let a := P.freeAlgebraAdjunction
  let f := complexSphereToDisk A (c.π i)
  let d := c.cell i
  let b := c.cofan₁.inj i ≫ c.g₁
  have h : P.freeAlgebraFunctor.map f ≫ d = b ≫ g := by
    dsimp only [d, b, f, AttachCells.cell_def]
    calc
      _ = (c.cofan₁.inj i ≫ c.m) ≫ c.g₂ := by rw [c.hm, Category.assoc]
      _ = _ := by rw [Category.assoc, ← c.isPushout.w, Category.assoc]
  have h' : f ≫ a.homEquiv _ _ d =
      a.homEquiv _ _ b ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P).map g := by
    rw [← a.homEquiv_naturality_left, ← a.homEquiv_naturality_right, h]
  change Y.carrier.d (c.π i) (c.π i + 1) (complexDiskHomEquiv A _ _ (a.homEquiv _ _ d)) =
    g.hom.f (c.π i + 1) (complexSphereHomEquiv A _ _ (a.homEquiv _ _ b)).val
  rw [← complexSphereToDisk_comp, h']
  exact complexSphereHomEquiv_naturality_val A _ _ _

/-- Two maps out of a cell attachment agree if they agree on the old algebra and new generators. -/
lemma attachedGenerator_hom_ext {Z : P.Algebra} {p q : Y ⟶ Z}
    (h₀ : g ≫ p = g ≫ q)
    (h : ∀ i, p.hom.f (c.π i) (attachedGenerator c i) =
      q.hom.f (c.π i) (attachedGenerator c i)) : p = q := by
  apply c.hom_ext h₀
  intro i
  let a := P.freeAlgebraAdjunction
  apply (a.homEquiv _ _).injective
  rw [a.homEquiv_naturality_right, a.homEquiv_naturality_right]
  apply (complexDiskHomEquiv A Z.carrier (c.π i)).injective
  rw [complexDiskHomEquiv_naturality, complexDiskHomEquiv_naturality]
  exact h i

/-- 境界と両立する先行段の射と新生成元の像から、付加後の代数の射を得る。 -/
lemma exists_attachedGenerator_map {Z : P.Algebra} (h : X ⟶ Z)
    (v : ∀ i : c.ι, Z.carrier.X (c.π i))
    (hv : ∀ i, Z.carrier.d (c.π i) (c.π i + 1) (v i) =
      h.hom.f (c.π i + 1) (attachedBoundary c i).val) :
    ∃ k : Y ⟶ Z, g ≫ k = h ∧
      ∀ i, k.hom.f (c.π i) (attachedGenerator c i) = v i := by
  let a := P.freeAlgebraAdjunction
  let d (i : c.ι) := (a.homEquiv (complexDisk A (c.π i)) Z).symm
    ((complexDiskHomEquiv A Z.carrier (c.π i)).symm (v i))
  let D := Cofan.mk Z d
  let p := c.isColimit₂.desc D
  have hp (i : c.ι) : c.cofan₂.inj i ≫ p = d i :=
    c.isColimit₂.fac D (Discrete.mk i)
  have hd (i : c.ι) : a.homEquiv _ _ (d i) =
      (complexDiskHomEquiv A Z.carrier (c.π i)).symm (v i) :=
    (a.homEquiv _ _).apply_symm_apply _
  have hw : c.g₁ ≫ h = c.m ≫ p := by
    apply Cofan.IsColimit.hom_ext c.isColimit₁
    intro i
    rw [← Category.assoc (c.cofan₁.inj i) c.g₁ h,
      ← Category.assoc (c.cofan₁.inj i) c.m p, c.hm i,
      Category.assoc (P.freeAlgebraFunctor.map (complexSphereToDisk A (c.π i))), hp]
    apply (a.homEquiv _ _).injective
    rw [a.homEquiv_naturality_right, a.homEquiv_naturality_left, hd]
    apply (complexSphereHomEquiv A Z.carrier (c.π i + 1)).injective
    apply Subtype.ext
    rw [complexSphereHomEquiv_naturality_val, complexSphereToDisk_comp,
      Equiv.apply_symm_apply]
    exact (hv i).symm
  let k := c.isPushout.desc h p hw
  refine ⟨k, c.isPushout.inl_desc h p hw, fun i => ?_⟩
  have hk : c.cell i ≫ k = d i := by
    rw [AttachCells.cell_def, Category.assoc, c.isPushout.inr_desc, hp]
  have he := congrArg (fun z => complexDiskHomEquiv A Z.carrier (c.π i)
    (a.homEquiv _ _ z)) hk
  rw [a.homEquiv_naturality_right, complexDiskHomEquiv_naturality, hd,
    Equiv.apply_symm_apply] at he
  exact he

end SerrePositivity.EInfinity.Operad
