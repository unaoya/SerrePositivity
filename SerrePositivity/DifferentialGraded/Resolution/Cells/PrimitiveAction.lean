module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.PrimitiveData
public import SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochain
public import SerrePositivity.DifferentialGraded.Complexes.TensorCochainInterchange

/-! # 指定原始元の後方Homへの作用と境界作用

## 概要
指定原始元の後方Homへの作用と境界作用。

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
universe u v w z
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {I : Type w}
  {C : Family A D I} {E : Type z} [DGCategory A E] {F : DGFunctor A D E}
variable (P : PrimitiveData A D I C E F)

def primitiveAction (i : I) (y : E) :
    Cochain (C.generator A D I i ⊗ homObject A E (F.obj (C.target i)) y)
      (homObject A E (F.obj (C.source i)) y) 0 :=
  ((tensorRightHom (homObject A E (F.obj (C.target i)) y) (C.generator A D I i)
    (homObject A E (F.obj (C.source i)) (F.obj (C.target i)))).f 0 (P.cochain i)).comp
    (Cochain.ofHom (eComp (Complex A) (F.obj (C.source i)) (F.obj (C.target i)) y))
      (zero_add 0)

/-- 境界をFで写して後方Homと合成するchain map。 -/
def boundaryOriginalAction (_P : PrimitiveData A D I C E F) (i : I) (y : E) :
    homObject A D (C.source i) (C.target i) ⊗ homObject A E (F.obj (C.target i)) y ⟶
      homObject A E (F.obj (C.source i)) y :=
  (F.map (C.source i) (C.target i) ▷ homObject A E (F.obj (C.target i)) y) ≫
    eComp (Complex A) (F.obj (C.source i)) (F.obj (C.target i)) y

lemma primitiveAction_differential (i : I) (y : E) :
    δ 0 1 (P.primitiveAction i y) =
    ((tensorRightHom (homObject A E (F.obj (C.target i)) y) (C.generator A D I i)
      (homObject A D (C.source i) (C.target i))).f 1 (C.boundaryCochain A D I i)).comp
      (Cochain.ofHom (P.boundaryOriginalAction i y)) (add_zero 1) := by
  rw [primitiveAction, δ_comp_ofHom,
    homComplexMap_differential (tensorRightHom _ _ _) 0 1,
    cochain_differential, tensorRightHom_cochain_comp, tensorRightHom_ofHom,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp]
  rfl

lemma primitiveAction_evaluate (i : I) (y : E) (T : Complex A)
    (f : Cochain T (homObject A E (F.obj (C.target i)) y) 0) :
    (tensorZeroCochain (P.cochain i) f).comp
      (Cochain.ofHom (eComp (Complex A) (F.obj (C.source i)) (F.obj (C.target i)) y))
        (zero_add 0) =
    ((tensorLeftHom (C.generator A D I i) T (homObject A E (F.obj (C.target i)) y)).f 0 f).comp
      (P.primitiveAction i y) (zero_add 0) := by
  have h := tensorCochain_interchange (C.generator A D I i)
    (homObject A E (F.obj (C.source i)) (F.obj (C.target i)))
    T (homObject A E (F.obj (C.target i)) y) 0 0 0 (zero_add 0) (zero_add 0)
    (P.cochain i) f
  simp only [mul_zero, Int.negOnePow_zero, one_smul] at h
  rw [tensorZeroCochain, h, Cochain.comp_assoc_of_third_is_zero_cochain]
  rfl

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
