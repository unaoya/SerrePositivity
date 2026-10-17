module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.GeneratorBoundary

/-! # cell生成元が与えるdiskと指定境界の可換square

## 概要
cell生成元が与えるdiskと指定境界の可換square。

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
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : Family A D I)

/-- 追加した生成元とその微分を持つ実際のdisk射。 -/
def generatorDisk (i : I) :
    complexDisk A (C.degree i) ⟶ C.attachedHom A D I (C.source i) (C.target i) :=
  (complexDiskHomEquiv A _ (C.degree i)).symm (C.generatorElement A D I i)

lemma generatorDisk_generator (i : I) :
    complexDiskHomEquiv A (C.attachedHom A D I (C.source i) (C.target i))
      (C.degree i) (C.generatorDisk A D I i) = C.generatorElement A D I i :=
  (complexDiskHomEquiv A _ (C.degree i)).apply_symm_apply _

/-- sphere境界を元のHomへ入れる射は、付加したdiskを通る。 -/
lemma generatorDisk_boundary (i : I) :
    complexSphereToDisk A (C.degree i) ≫ C.generatorDisk A D I i =
    complexSphereMap A (C.degree i + 1) (C.boundary i) ≫
      C.originalHomInclusion A D I (C.source i) (C.target i) := by
  apply (complexSphereHomEquiv A _ (C.degree i + 1)).injective
  apply Subtype.ext
  rw [complexSphereToDisk_comp, generatorDisk_generator, differential_generatorElement]
  change _ = (complexSphereCycle A (C.degree i + 1)
    (complexSphereMap A (C.degree i + 1) (C.boundary i) ≫
      C.originalHomInclusion A D I (C.source i) (C.target i))).val
  rw [complexSphereCycle_comp]
  have h : (complexSphereCycle A (C.degree i + 1)
      (complexSphereMap A (C.degree i + 1) (C.boundary i))).val = (C.boundary i).val :=
    congrArg Subtype.val ((complexSphereHomEquiv A _ (C.degree i + 1)).apply_symm_apply _)
  rw [h]

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
