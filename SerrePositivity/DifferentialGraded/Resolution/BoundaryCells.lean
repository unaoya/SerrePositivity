module
public import SerrePositivity.DifferentialGraded.Resolution.Initial
public import SerrePositivity.DifferentialGraded.Complexes.CellCriterion

/-! # dg圏解像度で付加する境界cellの添字と増大square

## 概要
sourceのcycleの像がtargetで境界である証人を保持する。
これはcell付加の入力であり、dg圏のpushoutや追加微分の構成ではない。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A]

/-- 次数q+1のcycleと、その増大像の次数qの原始元。 -/
structure ComplexBoundaryCell {K L : Complex A} (f : K ⟶ L) where
  degree : ℤ
  cycle : complexCycles A K (degree + 1)
  primitive : L.X degree
  boundary : L.d degree (degree + 1) primitive = f.f (degree + 1) cycle.val

namespace ComplexBoundaryCell
variable {K L : Complex A} {f : K ⟶ L} (c : ComplexBoundaryCell A f)

def attachingMap : complexSphere A (c.degree + 1) ⟶ K :=
  complexSphereMap A (c.degree + 1) c.cycle

def targetDiskMap : complexDisk A c.degree ⟶ L :=
  (complexDiskHomEquiv A L c.degree).symm c.primitive

lemma targetDiskMap_generator :
    complexDiskHomEquiv A L c.degree (c.targetDiskMap A) = c.primitive :=
  (complexDiskHomEquiv A L c.degree).apply_symm_apply c.primitive

/-- cellの境界包含と増大の可換square。新生成元の増大像は指定した原始元になる。 -/
lemma augmentation_square :
    c.attachingMap A ≫ f = complexSphereToDisk A c.degree ≫ c.targetDiskMap A := by
  apply (complexSphereHomEquiv A L (c.degree + 1)).injective
  apply Subtype.ext
  change (complexSphereCycle A (c.degree + 1) (c.attachingMap A ≫ f)).val = _
  rw [complexSphereCycle_comp]
  have hc : (complexSphereCycle A (c.degree + 1) (c.attachingMap A)).val = c.cycle.val :=
    congrArg Subtype.val ((complexSphereHomEquiv A K (c.degree + 1)).apply_symm_apply c.cycle)
  rw [hc]
  change f.f (c.degree + 1) c.cycle.val =
    (complexSphereHomEquiv A L (c.degree + 1)
      (complexSphereToDisk A c.degree ≫ c.targetDiskMap A)).val
  rw [complexSphereToDisk_comp, targetDiskMap_generator]
  exact c.boundary.symm

/-- sourceで境界を埋め、指定target原始元へ厳密に送られる条件。 -/
def HasFilling : Prop :=
  ∃ t : K.X c.degree, K.d c.degree (c.degree + 1) t = c.cycle.val ∧
    f.f c.degree t = c.primitive

/-- 全cellを埋める複体射は準同型。存在はこの条件に含めていない。 -/
lemma quasiIso_of_filling (h : ∀ c : ComplexBoundaryCell A f, c.HasFilling A) : QuasiIso f := by
  apply complex_quasiIso_of_boundary_lifting A f
  intro n z y hy
  exact h ⟨n, z, y, hy.symm⟩

end ComplexBoundaryCell

namespace DGCategoryBoundaryCells
variable (S : Type v) (D : Type w) [DGCategory A S] [DGCategory A D]

/-- 全対象対の全cycleとtarget原始元を同時に付加するための添字。 -/
abbrev Index (F : DGFunctor A S D) := Σ x : S, Σ y : S, ComplexBoundaryCell A (F.map x y)

instance indexSmall [Small.{u} S] (F : DGFunctor A S D) : Small.{u} (Index A S D F) :=
  inferInstance

end DGCategoryBoundaryCells
end SerrePositivity.DifferentialGraded
