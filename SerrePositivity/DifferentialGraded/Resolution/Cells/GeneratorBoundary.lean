module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Category
public import SerrePositivity.DifferentialGraded.Complexes.RightUnitorEvaluation
public import SerrePositivity.DifferentialGraded.Complexes.HomMapEvaluation

/-! # 任意次数cell生成元の指定境界方程式

## 概要
任意次数cell生成元の指定境界方程式。

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
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w)
variable (C : Family A D I)

lemma generatorTerm_apply (i : I) (e : (C.generator A D I i).X (C.degree i)) :
    (C.generatorTerm A D I i).f (C.degree i) e =
    ιTensorObj (homObject A D (C.source i) (C.source i))
      (C.generator A D I i ⊗ homObject A D (C.target i) (C.target i))
      0 (C.degree i) (C.degree i) (zero_add _)
      ((unitElement A (C.source i)).val ⊗ₜ[A]
        ιTensorObj (C.generator A D I i) (homObject A D (C.target i) (C.target i))
          (C.degree i) 0 (C.degree i) (add_zero _)
          (e ⊗ₜ[A] (unitElement A (C.target i)).val)) := by
  unfold generatorTerm
  dsimp only [term]
  rw [chain_comp_apply, complexLeftUnitor_inv_apply, tensorMap_apply,
    chain_comp_apply, complexRightUnitor_inv_apply, tensorMap_apply]
  rfl

/-- 中間和次数を明示した両側単位の評価。 -/
lemma forward_units_of_sum {x y : D} {n a : ℤ} (ha : 0 + n = a) (hn : a + 0 = n)
    (f : GradedHom A x y n) :
    forward A (forward A (unitElement A x).val f ha) (unitElement A y).val hn = f := by
  have h : a = n := by omega
  subst h
  rw [forward_unit, unit_forward]

lemma replaceFirst_generatorTerm (i : I) :
    (C.replaceFirst A D I i [] (C.source i) (C.target i)).v
      (C.degree i) (C.degree i + 1) rfl
      ((C.generatorTerm A D I i).f (C.degree i)
        ((singleObjXSelf (.up ℤ) (C.degree i) (𝟙_ (ModuleCat.{u} A))).inv (1 : A))) =
    (C.boundary i).val := by
  change ((C.replaceMiddle A D I i (homObject A D (C.source i) (C.source i))
      (homObject A D (C.target i) (C.target i))).comp
    (Cochain.ofHom ((α_ (homObject A D (C.source i) (C.source i))
      (homObject A D (C.source i) (C.target i))
      (homObject A D (C.target i) (C.target i))).inv ≫
      eComp (Complex A) (C.source i) (C.source i) (C.target i) ▷
        homObject A D (C.target i) (C.target i) ≫
      eComp (Complex A) (C.source i) (C.target i) (C.target i))) (add_zero 1)).v
      (C.degree i) (C.degree i + 1) rfl
      ((C.generatorTerm A D I i).f (C.degree i)
        ((singleObjXSelf (.up ℤ) (C.degree i) (𝟙_ (ModuleCat.{u} A))).inv (1 : A))) = _
  rw [generatorTerm_apply, cochain_comp_ofHom_apply]
  rw [replaceMiddle, tensorLeftHom_apply_of_sum
    (homObject A D (C.source i) (C.source i))
    (C.generator A D I i ⊗ homObject A D (C.target i) (C.target i))
    (homObject A D (C.source i) (C.target i) ⊗ homObject A D (C.target i) (C.target i))
    1 0 (C.degree i) (C.degree i) (C.degree i + 1) (C.degree i + 1)
    (zero_add _) rfl rfl, tensorRightHom_apply,
    boundaryCochain_generator, mul_zero, Int.negOnePow_zero, one_smul]
  simp only [chain_comp_apply]
  rw [associator_inv_apply, whiskerRight_apply]
  change forward A (forward A (unitElement A (C.source i)).val (C.boundary i).val rfl)
    (unitElement A (C.target i)).val (by omega) = _
  exact forward_units_of_sum A D rfl (by omega) (C.boundary i).val

variable [Small.{u} I]

/-- 最終Homの生成cell。閉じているとは仮定しない。 -/
def generatorElement (i : I) : (C.attachedHom A D I (C.source i) (C.target i)).X (C.degree i) :=
  (C.generatorInclusion A D I i).f (C.degree i)
    ((singleObjXSelf (.up ℤ) (C.degree i) (𝟙_ (ModuleCat.{u} A))).inv (1 : A))

lemma replaceRow_singleton (i : I) (x y : D) :
    C.replaceRow A D I [i] x y = (C.replaceFirst A D I i [] x y).comp
      (Cochain.ofHom (C.originalHom A D I x y)) (add_zero 1) := by
  simp only [replaceRow, List.length_cons, List.length_nil, zero_add, Finset.range_one,
    Finset.sum_singleton]
  rfl

lemma replacement_generatorElement (i : I) :
    (C.replacement A D I (C.source i) (C.target i)).v
      (C.degree i) (C.degree i + 1) rfl (C.generatorElement A D I i) =
    (C.originalHom A D I (C.source i) (C.target i)).f (C.degree i + 1) (C.boundary i).val := by
  have h := congrArg (fun f : Cochain (C.term A D I [i] (C.source i) (C.target i))
      (C.internalHom A D I (C.source i) (C.target i)) 1 =>
      f.v (C.degree i) (C.degree i + 1) rfl ((C.generatorTerm A D I i).f (C.degree i)
        ((singleObjXSelf (.up ℤ) (C.degree i) (𝟙_ (ModuleCat.{u} A))).inv (1 : A))))
    (C.replacement_precomp A D I [i] (C.source i) (C.target i))
  rw [replaceRow_singleton, cochain_ofHom_comp_apply, cochain_comp_ofHom_apply,
    replaceFirst_generatorTerm] at h
  exact h

lemma internal_d_generatorElement (i : I) :
    (C.internalHom A D I (C.source i) (C.target i)).d (C.degree i) (C.degree i + 1)
      (C.generatorElement A D I i) = 0 :=
  (complexSphereCycle A (C.degree i) (C.generatorInclusion A D I i)).property

/-- 付加した次数qの生成元の微分は元のHom内の指定(q+1)-cycle。 -/
lemma differential_generatorElement (i : I) :
    (C.attachedHom A D I (C.source i) (C.target i)).d (C.degree i) (C.degree i + 1)
      (C.generatorElement A D I i) =
    (C.originalHomInclusion A D I (C.source i) (C.target i)).f (C.degree i + 1)
      (C.boundary i).val := by
  rw [attachedHom_d]
  change (C.internalHom A D I (C.source i) (C.target i)).d (C.degree i) (C.degree i + 1)
      (C.generatorElement A D I i) +
    (C.replacement A D I (C.source i) (C.target i)).v (C.degree i) (C.degree i + 1) rfl
      (C.generatorElement A D I i) = _
  rw [internal_d_generatorElement, zero_add, replacement_generatorElement]
  rfl

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
