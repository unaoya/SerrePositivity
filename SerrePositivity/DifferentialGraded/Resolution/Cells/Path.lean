module

public import SerrePositivity.DifferentialGraded.Resolution.Cells.Length
public import SerrePositivity.DifferentialGraded.Complexes.RightUnitorEvaluation
public import SerrePositivity.DifferentialGraded.Complexes.HomMapEvaluation
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Append.Recursion
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Boundary
public import SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochain
public import SerrePositivity.DifferentialGraded.Functor.Components
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoinEvaluation
public import SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochainEvaluation
public import SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochainLeftMap
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Append.BoundaryCompatibility
public import SerrePositivity.DifferentialGraded.Complexes.PerturbationMap
public import SerrePositivity.DifferentialGraded.Complexes.SphereCochainExt

/-!
# Resolution.Cells.Path

## 概要
20 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## GeneratorBoundary（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/GeneratorBoundary.lean） -/

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

@[expose] public section GeneratorBoundary
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end GeneratorBoundary

/-! ## GeneratorDisk（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/GeneratorDisk.lean） -/

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

@[expose] public section GeneratorDisk
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end GeneratorDisk

/-! ## PathGeneration（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/PathGeneration.lean） -/

/-! # 元のHomと任意次数生成cellの反復合成によるpath生成式

## 概要
元のHomと任意次数生成cellの反復合成によるpath生成式。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section PathGeneration
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : Family A D I)

lemma prefixPath_generator (i : I) (x y : D) (p q b n : ℤ)
    (hb : C.degree i + q = b) (hn : p + b = n) (a : (homObject A D x (C.source i)).X p)
    (t : (C.internalHom A D I (C.target i) y).X q) :
    (C.prefixPath A D I i x y).f n
      (ιTensorObj (homObject A D x (C.source i))
        (C.generator A D I i ⊗ C.internalHom A D I (C.target i) y) p b n hn (a ⊗ₜ[A]
          ιTensorObj (C.generator A D I i) (C.internalHom A D I (C.target i) y)
            (C.degree i) q b hb
            ((singleObjXSelf (.up ℤ) (C.degree i) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] t))) =
    forward A (x := (⟨x⟩ : C.Objects A D I)) (y := ⟨C.source i⟩) (z := ⟨y⟩)
      ((C.originalHomInclusion A D I x (C.source i)).f p a)
      (forward A (x := (⟨C.source i⟩ : C.Objects A D I)) (y := ⟨C.target i⟩) (z := ⟨y⟩)
        (C.generatorElement A D I i) t hb) hn := by
  have hp : (C.originalHom A D I x (C.source i) ▷ C.internalHom A D I (C.source i) y) ≫
      C.internalComposition A D I x (C.source i) y = C.internalPrepend A D I x (C.source i) y :=
    C.internalComposition_left_inclusion A D I [] x (C.source i) y
  have hg := C.prefixPath_generated A D I i x y
  rw [← hp] at hg
  have h := congrArg (fun f : homObject A D x (C.source i) ⊗
      (C.generator A D I i ⊗ C.internalHom A D I (C.target i) y) ⟶ C.internalHom A D I x y =>
    f.f n (ιTensorObj (homObject A D x (C.source i))
      (C.generator A D I i ⊗ C.internalHom A D I (C.target i) y) p b n hn (a ⊗ₜ[A]
        ιTensorObj (C.generator A D I i) (C.internalHom A D I (C.target i) y)
          (C.degree i) q b hb
          ((singleObjXSelf (.up ℤ) (C.degree i) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] t)))) hg
  simp only [chain_comp_apply, whiskerLeft_apply, whiskerRight_apply] at h
  change _ = (C.attachedComposition A D I x (C.source i) y).f n
    (ιTensorObj (C.attachedHom A D I x (C.source i)) (C.attachedHom A D I (C.source i) y)
      p b n hn ((C.originalHomInclusion A D I x (C.source i)).f p a ⊗ₜ[A]
        (C.attachedComposition A D I (C.source i) (C.target i) y).f b
          (ιTensorObj (C.attachedHom A D I (C.source i) (C.target i))
            (C.attachedHom A D I (C.target i) y) (C.degree i) q b hb
            (C.generatorElement A D I i ⊗ₜ[A] t))))
  rw [attachedComposition_apply, attachedComposition_apply, originalHomInclusion_f]
  exact h.symm

lemma path_inclusion_generator (i : I) (w : List I) (x y : D) (p q b n : ℤ)
    (hb : C.degree i + q = b) (hn : p + b = n) (a : (homObject A D x (C.source i)).X p)
    (t : (C.term A D I w (C.target i) y).X q) :
    (C.inclusion A D I (i :: w) x y).f n
      (ιTensorObj (homObject A D x (C.source i))
        (C.generator A D I i ⊗ C.term A D I w (C.target i) y) p b n hn (a ⊗ₜ[A]
          ιTensorObj (C.generator A D I i) (C.term A D I w (C.target i) y)
            (C.degree i) q b hb
            ((singleObjXSelf (.up ℤ) (C.degree i) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] t))) =
    forward A (x := (⟨x⟩ : C.Objects A D I)) (y := ⟨C.source i⟩) (z := ⟨y⟩)
      ((C.originalHomInclusion A D I x (C.source i)).f p a)
      (forward A (x := (⟨C.source i⟩ : C.Objects A D I)) (y := ⟨C.target i⟩) (z := ⟨y⟩)
        (C.generatorElement A D I i) ((C.inclusion A D I w (C.target i) y).f q t) hb) hn := by
  have h := congrArg (fun f : homObject A D x (C.source i) ⊗
      (C.generator A D I i ⊗ C.term A D I w (C.target i) y) ⟶ C.internalHom A D I x y =>
    f.f n (ιTensorObj (homObject A D x (C.source i))
      (C.generator A D I i ⊗ C.term A D I w (C.target i) y) p b n hn (a ⊗ₜ[A]
        ιTensorObj (C.generator A D I i) (C.term A D I w (C.target i) y) (C.degree i) q b hb
          ((singleObjXSelf (.up ℤ) (C.degree i) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] t))))
    (C.prefixPath_inclusion A D I i x y w)
  simp only [chain_comp_apply, whiskerLeft_apply] at h
  exact h.symm.trans (C.prefixPath_generator A D I i x y p q b n hb hn a
    ((C.inclusion A D I w (C.target i) y).f q t))

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end PathGeneration

/-! ## PathEvaluation（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/PathEvaluation.lean） -/

/-! # 指定原始元による任意次数cell pathの評価

## 概要
指定原始元による任意次数cell pathの評価。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section PathEvaluation
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {I : Type w}
  {C : Family A D I} {E : Type z} [DGCategory A E] {F : DGFunctor A D E}
variable (P : PrimitiveData A D I C E F)

/-- 既存HomをFで写し、生成cellを指定原始元へ写して順に合成する。 -/
def pathEvaluation : ∀ (w : List I) (x y : D),
    Cochain (C.term A D I w x y) (homObject A E (F.obj x) (F.obj y)) 0
  | [], x, y => Cochain.ofHom (F.map x y)
  | i :: w, x, y =>
    (tensorZeroCochain (Cochain.ofHom (F.map x (C.source i)))
      ((tensorZeroCochain (P.cochain i) (pathEvaluation w (C.target i) y)).comp
        (Cochain.ofHom (eComp (Complex A) (F.obj (C.source i))
          (F.obj (C.target i)) (F.obj y))) (zero_add 0))).comp
      (Cochain.ofHom (eComp (Complex A) (F.obj x)
        (F.obj (C.source i)) (F.obj y))) (zero_add 0)

lemma pathEvaluation_nil (x y : D) :
    P.pathEvaluation [] x y = Cochain.ofHom (F.map x y) := rfl

lemma pathEvaluation_cons_generator (i : I) (w : List I) (x y : D)
    (p q b n : ℤ) (hb : C.degree i + q = b) (hn : p + b = n)
    (f : (homObject A D x (C.source i)).X p)
    (t : (C.term A D I w (C.target i) y).X q) :
    (P.pathEvaluation (i :: w) x y).v n n (add_zero n)
      (ιTensorObj (homObject A D x (C.source i))
        (C.generator A D I i ⊗ C.term A D I w (C.target i) y) p b n hn
        (f ⊗ₜ[A] ιTensorObj (C.generator A D I i) (C.term A D I w (C.target i) y)
          (C.degree i) q b hb
          ((singleObjXSelf (.up ℤ) (C.degree i) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] t))) =
    forward A ((F.map x (C.source i)).f p f)
      (forward A (P.primitive i)
        ((P.pathEvaluation w (C.target i) y).v q q (add_zero q) t) hb) hn := by
  subst hb
  change ((tensorZeroCochain (Cochain.ofHom (F.map x (C.source i)))
      ((tensorZeroCochain (P.cochain i) (P.pathEvaluation w (C.target i) y)).comp
        (Cochain.ofHom (eComp (Complex A) (F.obj (C.source i))
          (F.obj (C.target i)) (F.obj y))) (zero_add 0))).comp
      (Cochain.ofHom (eComp (Complex A) (F.obj x)
        (F.obj (C.source i)) (F.obj y))) (zero_add 0)).v n n (add_zero n)
      (ιTensorObj (homObject A D x (C.source i))
        (C.generator A D I i ⊗ C.term A D I w (C.target i) y) p (C.degree i + q) n hn
        (f ⊗ₜ[A] ιTensorObj (C.generator A D I i) (C.term A D I w (C.target i) y)
          (C.degree i) q (C.degree i + q) rfl
          ((singleObjXSelf (.up ℤ) (C.degree i) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] t))) = _
  rw [cochain_comp_ofHom_apply, tensorZeroCochain_apply,
    cochain_comp_ofHom_apply, tensorZeroCochain_apply, cochain_generator]
  rfl

/-- 両側に単位を持つ一生成元pathの評価は指定原始元そのもの。 -/
lemma pathEvaluation_generatorTerm (i : I) :
    (P.pathEvaluation [i] (C.source i) (C.target i)).v
      (C.degree i) (C.degree i) (add_zero _)
      ((C.generatorTerm A D I i).f (C.degree i)
        ((singleObjXSelf (.up ℤ) (C.degree i) (𝟙_ (ModuleCat.{u} A))).inv (1 : A))) =
    P.primitive i := by
  have he := congrArg (fun t : (C.term A D I [i] (C.source i) (C.target i)).X (C.degree i) =>
    (P.pathEvaluation [i] (C.source i) (C.target i)).v (C.degree i) (C.degree i) (add_zero _) t)
    (C.generatorTerm_apply A D I i
      ((singleObjXSelf (.up ℤ) (C.degree i) (𝟙_ (ModuleCat.{u} A))).inv (1 : A)))
  have h := P.pathEvaluation_cons_generator i [] (C.source i) (C.target i)
    0 0 (C.degree i) (C.degree i) (add_zero _) (zero_add _)
      (unitElement A (C.source i)).val
      (unitElement A (C.target i)).val
  simp only [Family.term_nil, pathEvaluation_nil, Cochain.ofHom_v,
    DGFunctor.map_unitElement, unit_forward, forward_unit] at h
  exact he.trans h

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
end

end PathEvaluation

/-! ## PathEvaluationPrepend（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/PathEvaluationPrepend.lean） -/

/-! # 元のHomを先頭合成する操作と有限path評価の整合性

## 概要
元のHomを先頭合成する操作と有限path評価の整合性。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section PathEvaluationPrepend
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {I : Type w}
  {C : Family A D I} {E : Type z} [DGCategory A E] {F : DGFunctor A D E}
variable (P : PrimitiveData A D I C E F)

lemma pathEvaluation_prepend (w : List I) (x y z : D) :
    (Cochain.ofHom (C.prependMap A D I w x y z)).comp (P.pathEvaluation w x z) (zero_add 0) =
    (tensorZeroCochain (Cochain.ofHom (F.map x y)) (P.pathEvaluation w y z)).comp
      (Cochain.ofHom (eComp (Complex A) (F.obj x)
        (F.obj y) (F.obj z))) (zero_add 0) := by
  cases w with
  | nil =>
    simpa only [pathEvaluation_nil, Family.prependMap, tensorZeroCochain_ofHom,
      ← Cochain.ofHom_comp] using
      congrArg (fun f => Cochain.ofHom f) (F.map_comp x y z)
  | cons b w =>
    have h := tensorJoin_evaluation
      (homObject A D x y) (homObject A D y (C.source b)) (homObject A D x (C.source b))
      (homObject A E (F.obj x) (F.obj y))
      (homObject A E (F.obj y) (F.obj (C.source b)))
      (homObject A E (F.obj x) (F.obj (C.source b)))
      (C.generator A D I b ⊗ C.term A D I w (C.target b) z)
      (homObject A E (F.obj (C.source b)) (F.obj z))
      (homObject A E (F.obj y) (F.obj z))
      (homObject A E (F.obj x) (F.obj z))
      (F.map x y) (F.map y (C.source b)) (F.map x (C.source b))
      (eComp (Complex A) x y (C.source b))
      (eComp (Complex A) (F.obj x) (F.obj y) (F.obj (C.source b)))
      (eComp (Complex A) (F.obj x) (F.obj (C.source b)) (F.obj z))
      (eComp (Complex A) (F.obj y) (F.obj (C.source b)) (F.obj z))
      (eComp (Complex A) (F.obj x) (F.obj y) (F.obj z))
      (F.map_comp x y (C.source b))
      (e_assoc' (Complex A) (F.obj x) (F.obj y)
        (F.obj (C.source b)) (F.obj z)).symm
      ((tensorZeroCochain (P.cochain b) (P.pathEvaluation w (C.target b) z)).comp
        (Cochain.ofHom (eComp (Complex A) (F.obj (C.source b))
          (F.obj (C.target b)) (F.obj z))) (zero_add 0))
    simpa only [pathEvaluation, prependMap, tensorHom_id] using h

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
end

end PathEvaluationPrepend

/-! ## PathEvaluationAppend（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/PathEvaluationAppend.lean） -/

/-! # 指定原始元による評価は任意二pathの連結を保つ

## 概要
指定原始元による評価は任意二pathの連結を保つ。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section PathEvaluationAppend
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {I : Type w}
  {C : Family A D I} {E : Type z} [DGCategory A E] {F : DGFunctor A D E}
variable (P : PrimitiveData A D I C E F)

lemma pathEvaluation_append (w v : List I) (x y z : D) :
    (Cochain.ofHom (C.appendMap A D I w v x y z)).comp
      (P.pathEvaluation (w ++ v) x z) (zero_add 0) =
    (tensorZeroCochain (P.pathEvaluation w x y) (P.pathEvaluation v y z)).comp
      (Cochain.ofHom (eComp (Complex A) (F.obj x)
        (F.obj y) (F.obj z))) (zero_add 0) := by
  induction w generalizing x with
  | nil => simpa only [Family.appendMap, List.nil_append, pathEvaluation_nil] using
      P.pathEvaluation_prepend v x y z
  | cons b w ih =>
    have hinner := tensorCarry_evaluation (P.cochain b)
      (P.pathEvaluation w (C.target b) y) (P.pathEvaluation v y z)
      (P.pathEvaluation (w ++ v) (C.target b) z)
      (C.appendMap A D I w v (C.target b) y z)
      (eComp (Complex A) (F.obj (C.target b)) (F.obj y) (F.obj z))
      (eComp (Complex A) (F.obj (C.source b)) (F.obj (C.target b)) (F.obj y))
      (eComp (Complex A) (F.obj (C.source b)) (F.obj (C.target b)) (F.obj z))
      (eComp (Complex A) (F.obj (C.source b)) (F.obj y) (F.obj z))
      (ih (C.target b))
      (e_assoc' (Complex A) (F.obj (C.source b)) (F.obj (C.target b))
        (F.obj y) (F.obj z)).symm
    have h := tensorCarry_evaluation (Cochain.ofHom (F.map x (C.source b)))
      ((tensorZeroCochain (P.cochain b) (P.pathEvaluation w (C.target b) y)).comp
        (Cochain.ofHom (eComp (Complex A) (F.obj (C.source b))
          (F.obj (C.target b)) (F.obj y))) (zero_add 0))
      (P.pathEvaluation v y z)
      ((tensorZeroCochain (P.cochain b) (P.pathEvaluation (w ++ v) (C.target b) z)).comp
        (Cochain.ofHom (eComp (Complex A) (F.obj (C.source b))
          (F.obj (C.target b)) (F.obj z))) (zero_add 0))
      ((α_ (C.generator A D I b) (C.term A D I w (C.target b) y) (C.term A D I v y z)).hom ≫
        (C.generator A D I b) ◁ C.appendMap A D I w v (C.target b) y z)
      (eComp (Complex A) (F.obj (C.source b)) (F.obj y) (F.obj z))
      (eComp (Complex A) (F.obj x) (F.obj (C.source b)) (F.obj y))
      (eComp (Complex A) (F.obj x) (F.obj (C.source b)) (F.obj z))
      (eComp (Complex A) (F.obj x) (F.obj y) (F.obj z))
      hinner
      (e_assoc' (Complex A) (F.obj x) (F.obj (C.source b))
        (F.obj y) (F.obj z)).symm
    simpa only [pathEvaluation, appendMap, List.cons_append] using h

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
end

end PathEvaluationAppend

/-! ## InternalEvaluation（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/InternalEvaluation.lean） -/

/-! # 指定原始元付きdg関手による全path直和の評価cochain

## 概要
指定原始元付きdg関手による全path直和の評価cochain。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section InternalEvaluation
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {I : Type w} [Small.{u} I]
  {C : Family A D I} {E : Type z} [DGCategory A E] {F : DGFunctor A D E}
variable (P : PrimitiveData A D I C E F)

/-- 各有限pathの評価を貼り合わせた次数0 cochain。微分との整合性は別に証明する。 -/
def internalEvaluation (x y : D) :
    Cochain (C.internalHom A D I x y)
      (homObject A E (F.obj x) (F.obj y)) 0 :=
  C.pathCochainDesc A D I x y _ 0 (fun w => P.pathEvaluation w x y)

lemma internalEvaluation_precomp (x y : D) (w : List I) :
    (Cochain.ofHom (C.inclusion A D I w x y)).comp (P.internalEvaluation x y) (zero_add 0) =
      P.pathEvaluation w x y := C.pathCochainDesc_precomp A D I x y _ 0 _ w

lemma internalEvaluation_original (x y : D) :
    (Cochain.ofHom (C.originalHom A D I x y)).comp (P.internalEvaluation x y) (zero_add 0) =
      Cochain.ofHom (F.map x y) := P.internalEvaluation_precomp x y []

lemma internalEvaluation_generator (i : I) :
    (Cochain.ofHom (C.generatorInclusion A D I i)).comp
      (P.internalEvaluation (C.source i) (C.target i)) (zero_add 0) = P.cochain i := by
  rw [Family.generatorInclusion, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain, internalEvaluation_precomp]
  apply (Cochain.fromSingleEquiv (add_zero (C.degree i))).injective
  apply (moduleElementEquiv A _).injective
  change ((Cochain.ofHom (C.generatorTerm A D I i)).comp
      (P.pathEvaluation [i] (C.source i) (C.target i)) (zero_add 0)).v
      (C.degree i) (C.degree i) (add_zero _)
      ((singleObjXSelf (.up ℤ) (C.degree i) (𝟙_ (ModuleCat.{u} A))).inv (1 : A)) =
    (P.cochain i).v (C.degree i) (C.degree i) (add_zero _)
      ((singleObjXSelf (.up ℤ) (C.degree i) (𝟙_ (ModuleCat.{u} A))).inv (1 : A))
  rw [cochain_ofHom_comp_apply, pathEvaluation_generatorTerm, cochain_generator]

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
end

end InternalEvaluation

/-! ## InternalEvaluationComposition（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/InternalEvaluationComposition.lean） -/

/-! # 全path直和の評価は内部合成を保つ

## 概要
全path直和の評価は内部合成を保つ。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section InternalEvaluationComposition
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {I : Type w} [Small.{u} I]
  {C : Family A D I} {E : Type z} [DGCategory A E] {F : DGFunctor A D E}
variable (P : PrimitiveData A D I C E F)

lemma internalEvaluation_composition (x y z : D) :
    (Cochain.ofHom (C.internalComposition A D I x y z)).comp (P.internalEvaluation x z)
      (zero_add 0) =
    (tensorZeroCochain (P.internalEvaluation x y) (P.internalEvaluation y z)).comp
      (Cochain.ofHom (eComp (Complex A) (F.obj x)
        (F.obj y) (F.obj z))) (zero_add 0) := by
  apply C.tensorTwoPathCochain_ext A D I x y z 0
  intro w v
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    Family.internalComposition_inclusion, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain,
    internalEvaluation_precomp,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, tensorZeroCochain_precomp,
    internalEvaluation_precomp, internalEvaluation_precomp]
  exact P.pathEvaluation_append w v x y z

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
end

end InternalEvaluationComposition

/-! ## BoundaryActionEvaluation（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/BoundaryActionEvaluation.lean） -/

/-! # 原始元作用の微分と有限path先頭境界の評価

## 概要
原始元作用の微分と有限path先頭境界の評価。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BoundaryActionEvaluation
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {I : Type w}
  {C : Family A D I} {E : Type z} [DGCategory A E] {F : DGFunctor A D E}
variable (P : PrimitiveData A D I C E F)

lemma boundaryAction_pathEvaluation (i : I) (w : List I) (y : D) :
    ((tensorLeftHom (C.generator A D I i) (C.term A D I w (C.target i) y)
      (homObject A E (F.obj (C.target i)) (F.obj y))).f 0
        (P.pathEvaluation w (C.target i) y)).comp
      (δ 0 1 (P.primitiveAction i (F.obj y))) (zero_add 1) =
    (C.replaceHead A D I i w y).comp (P.pathEvaluation w (C.source i) y) (add_zero 1) := by
  have h := tensorCochain_interchange (C.generator A D I i)
    (homObject A D (C.source i) (C.target i))
    (C.term A D I w (C.target i) y) (homObject A E (F.obj (C.target i)) (F.obj y))
    1 0 1 (add_zero 1) (zero_add 1)
    (C.boundaryCochain A D I i) (P.pathEvaluation w (C.target i) y)
  simp only [mul_zero, Int.negOnePow_zero, one_smul] at h
  have he :
      ((tensorLeftHom (homObject A D (C.source i) (C.target i))
        (C.term A D I w (C.target i) y)
        (homObject A E (F.obj (C.target i)) (F.obj y))).f 0
          (P.pathEvaluation w (C.target i) y)).comp
        (Cochain.ofHom (P.boundaryOriginalAction i (F.obj y))) (zero_add 0) =
      (tensorZeroCochain (Cochain.ofHom (F.map (C.source i) (C.target i)))
        (P.pathEvaluation w (C.target i) y)).comp
        (Cochain.ofHom (eComp (Complex A) (F.obj (C.source i)) (F.obj (C.target i)) (F.obj y)))
          (zero_add 0) := by
    rw [boundaryOriginalAction, Cochain.ofHom_comp,
      ← Cochain.comp_assoc_of_third_is_zero_cochain, ← tensorZeroCochain_ofHom_left]
  rw [primitiveAction_differential, ← Cochain.comp_assoc_of_third_is_zero_cochain, ← h,
    Cochain.comp_assoc_of_third_is_zero_cochain, he, ← pathEvaluation_prepend,
    ← Cochain.comp_assoc_of_second_is_zero_cochain]
  rfl

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
end

end BoundaryActionEvaluation

/-! ## EvaluationPrefix（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/EvaluationPrefix.lean） -/

/-! # 前方Homと指定原始元による有限path評価作用

## 概要
前方Homと指定原始元による有限path評価作用。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section EvaluationPrefix
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {I : Type w}
  {C : Family A D I} {E : Type z} [DGCategory A E] {F : DGFunctor A D E}
variable (P : PrimitiveData A D I C E F)

def evaluationOriginalAction (_P : PrimitiveData A D I C E F) (x t y : D) :
    homObject A D x t ⊗ homObject A E (F.obj t) (F.obj y) ⟶
      homObject A E (F.obj x) (F.obj y) :=
  (F.map x t ▷ homObject A E (F.obj t) (F.obj y)) ≫
    eComp (Complex A) (F.obj x) (F.obj t) (F.obj y)

def evaluationPrefixAction (i : I) (x y : D) :
    Cochain (homObject A D x (C.source i) ⊗
      (C.generator A D I i ⊗ homObject A E (F.obj (C.target i)) (F.obj y)))
      (homObject A E (F.obj x) (F.obj y)) 0 :=
  ((tensorLeftHom (homObject A D x (C.source i))
    (C.generator A D I i ⊗ homObject A E (F.obj (C.target i)) (F.obj y))
    (homObject A E (F.obj (C.source i)) (F.obj y))).f 0
      (P.primitiveAction i (F.obj y))).comp
    (Cochain.ofHom (P.evaluationOriginalAction x (C.source i) y)) (zero_add 0)

lemma evaluationPrefixAction_differential (i : I) (x y : D) :
    δ 0 1 (P.evaluationPrefixAction i x y) =
    ((tensorLeftHom (homObject A D x (C.source i))
      (C.generator A D I i ⊗ homObject A E (F.obj (C.target i)) (F.obj y))
      (homObject A E (F.obj (C.source i)) (F.obj y))).f 1
        (δ 0 1 (P.primitiveAction i (F.obj y)))).comp
      (Cochain.ofHom (P.evaluationOriginalAction x (C.source i) y)) (add_zero 1) := by
  rw [evaluationPrefixAction, δ_comp_ofHom,
    homComplexMap_differential (tensorLeftHom _ _ _) 0 1]

lemma pathEvaluation_cons_action (i : I) (w : List I) (x y : D) :
    P.pathEvaluation (i :: w) x y =
    ((tensorLeftHom (homObject A D x (C.source i))
      (C.generator A D I i ⊗ C.term A D I w (C.target i) y)
      (C.generator A D I i ⊗ homObject A E (F.obj (C.target i)) (F.obj y))).f 0
      ((tensorLeftHom (C.generator A D I i) (C.term A D I w (C.target i) y)
        (homObject A E (F.obj (C.target i)) (F.obj y))).f 0
          (P.pathEvaluation w (C.target i) y))).comp
      (P.evaluationPrefixAction i x y) (zero_add 0) := by
  change (tensorZeroCochain (Cochain.ofHom (F.map x (C.source i)))
      ((tensorZeroCochain (P.cochain i) (P.pathEvaluation w (C.target i) y)).comp
        (Cochain.ofHom (eComp (Complex A) (F.obj (C.source i))
          (F.obj (C.target i)) (F.obj y))) (zero_add 0))).comp
      (Cochain.ofHom (eComp (Complex A) (F.obj x)
        (F.obj (C.source i)) (F.obj y))) (zero_add 0) = _
  rw [primitiveAction_evaluate, tensorZeroCochain_ofHom_left, tensorLeftHom_cochain_comp]
  simp only [Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp]
  rfl

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
end

end EvaluationPrefix

/-! ## InternalEvaluationPrefix（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/InternalEvaluationPrefix.lean） -/

/-! # 全path直和への前方Hom・任意次数生成元追加と評価の整合性

## 概要
全path直和への前方Hom・任意次数生成元追加と評価の整合性。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section InternalEvaluationPrefix
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {I : Type w} [Small.{u} I]
  {C : Family A D I} {E : Type z} [DGCategory A E] {F : DGFunctor A D E}
variable (P : PrimitiveData A D I C E F)

lemma internalEvaluation_prefixPath (b : I) (x y : D) :
    (Cochain.ofHom (C.prefixPath A D I b x y)).comp (P.internalEvaluation x y) (zero_add 0) =
    ((tensorLeftHom (homObject A D x (C.source b))
      (C.generator A D I b ⊗ C.internalHom A D I (C.target b) y)
      (C.generator A D I b ⊗ homObject A E (F.obj (C.target b)) (F.obj y))).f 0
      ((tensorLeftHom (C.generator A D I b) (C.internalHom A D I (C.target b) y)
        (homObject A E (F.obj (C.target b)) (F.obj y))).f 0
          (P.internalEvaluation (C.target b) y))).comp
      (P.evaluationPrefixAction b x y) (zero_add 0) := by
  apply C.prefixPathCochain_ext A D I b x y 0
  intro w
  have ht :
      (Cochain.ofHom ((homObject A D x (C.source b)) ◁
        ((C.generator A D I b) ◁ C.inclusion A D I w (C.target b) y))).comp
        ((tensorLeftHom (homObject A D x (C.source b))
          (C.generator A D I b ⊗ C.internalHom A D I (C.target b) y)
          (C.generator A D I b ⊗ homObject A E (F.obj (C.target b)) (F.obj y))).f 0
          ((tensorLeftHom (C.generator A D I b) (C.internalHom A D I (C.target b) y)
            (homObject A E (F.obj (C.target b)) (F.obj y))).f 0
              (P.internalEvaluation (C.target b) y))) (zero_add 0) =
      (tensorLeftHom (homObject A D x (C.source b))
        (C.generator A D I b ⊗ C.term A D I w (C.target b) y)
        (C.generator A D I b ⊗ homObject A E (F.obj (C.target b)) (F.obj y))).f 0
        ((tensorLeftHom (C.generator A D I b) (C.term A D I w (C.target b) y)
          (homObject A E (F.obj (C.target b)) (F.obj y))).f 0
            (P.pathEvaluation w (C.target b) y)) := by
    rw [← tensorLeftHom_ofHom (homObject A D x (C.source b)), ← tensorLeftHom_cochain_comp,
      ← tensorLeftHom_ofHom (C.generator A D I b), ← tensorLeftHom_cochain_comp,
      internalEvaluation_precomp]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    Family.prefixPath_inclusion, internalEvaluation_precomp,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, ht]
  exact P.pathEvaluation_cons_action b w x y

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
end

end InternalEvaluationPrefix

/-! ## PathEvaluationDifferential（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/PathEvaluationDifferential.lean） -/

/-! # 任意次数cell path評価の微分：先頭境界項と後方微分項

## 概要
任意次数cell path評価の微分：先頭境界項と後方微分項。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section PathEvaluationDifferential
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {I : Type w}
  {C : Family A D I} {E : Type z} [DGCategory A E] {F : DGFunctor A D E}
variable (P : PrimitiveData A D I C E F)

lemma evaluationPrefix_boundary (i : I) (w : List I) (x y : D) :
    ((tensorLeftHom (homObject A D x (C.source i))
      (C.generator A D I i ⊗ C.term A D I w (C.target i) y)
      (C.generator A D I i ⊗ homObject A E (F.obj (C.target i)) (F.obj y))).f 0
      ((tensorLeftHom (C.generator A D I i) (C.term A D I w (C.target i) y)
        (homObject A E (F.obj (C.target i)) (F.obj y))).f 0
          (P.pathEvaluation w (C.target i) y))).comp
      (δ 0 1 (P.evaluationPrefixAction i x y)) (zero_add 1) =
    (C.replaceFirst A D I i w x y).comp (P.pathEvaluation w x y) (add_zero 1) := by
  have he :
      ((tensorLeftHom (homObject A D x (C.source i)) (C.term A D I w (C.source i) y)
        (homObject A E (F.obj (C.source i)) (F.obj y))).f 0
          (P.pathEvaluation w (C.source i) y)).comp
        (Cochain.ofHom (P.evaluationOriginalAction x (C.source i) y)) (zero_add 0) =
      (Cochain.ofHom (C.prependMap A D I w x (C.source i) y)).comp
        (P.pathEvaluation w x y) (zero_add 0) := by
    rw [evaluationOriginalAction, Cochain.ofHom_comp,
      ← Cochain.comp_assoc_of_third_is_zero_cochain,
      ← tensorZeroCochain_ofHom_left, ← pathEvaluation_prepend]
  rw [evaluationPrefixAction_differential,
    ← Cochain.comp_assoc_of_third_is_zero_cochain,
    ← tensorLeftHom_cochain_comp, boundaryAction_pathEvaluation,
    tensorLeftHom_cochain_comp, Cochain.comp_assoc_of_third_is_zero_cochain, he,
    ← Cochain.comp_assoc_of_second_is_zero_cochain, ← Family.replaceFirst_eq_head]

/-- 後方の任意次数cochainを、先頭Hom・生成元の評価作用へ合成する。 -/
def pathEvaluationTail (i : I) (w : List I) (x y : D) (p : ℤ)
    (f : Cochain (C.term A D I w (C.target i) y)
      (homObject A E (F.obj (C.target i)) (F.obj y)) p) :
    Cochain (C.term A D I (i :: w) x y) (homObject A E (F.obj x) (F.obj y)) p :=
  ((tensorLeftHom (homObject A D x (C.source i))
    (C.generator A D I i ⊗ C.term A D I w (C.target i) y)
    (C.generator A D I i ⊗ homObject A E (F.obj (C.target i)) (F.obj y))).f p
    ((tensorLeftHom (C.generator A D I i) (C.term A D I w (C.target i) y)
      (homObject A E (F.obj (C.target i)) (F.obj y))).f p f)).comp
    (P.evaluationPrefixAction i x y) (add_zero p)

lemma pathEvaluation_cons_differential (i : I) (w : List I) (x y : D) :
    δ 0 1 (P.pathEvaluation (i :: w) x y) =
    (C.replaceFirst A D I i w x y).comp (P.pathEvaluation w x y) (add_zero 1) +
    P.pathEvaluationTail i w x y 1 (δ 0 1 (P.pathEvaluation w (C.target i) y)) := by
  rw [pathEvaluation_cons_action,
    δ_comp _ _ (zero_add 0) 1 1 1 (zero_add 1) (zero_add 1) (zero_add 1),
    evaluationPrefix_boundary,
    homComplexMap_differential (tensorLeftHom _ _ _) 0 1,
    homComplexMap_differential (tensorLeftHom _ _ _) 0 1]
  simp only [Int.negOnePow_zero, one_smul]
  rfl

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
end

end PathEvaluationDifferential

/-! ## EvaluationReplacement（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/EvaluationReplacement.lean） -/

/-! # 全path評価のHom微分と指定境界置換作用素の整合性

## 概要
全path評価のHom微分と指定境界置換作用素の整合性。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section EvaluationReplacement
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {I : Type w} [Small.{u} I]
  {C : Family A D I} {E : Type z} [DGCategory A E] {F : DGFunctor A D E}
variable (P : PrimitiveData A D I C E F)

lemma pathEvaluationTail_internalEvaluation (b : I) (w : List I) (x y : D) (p : ℤ)
    (f : Cochain (C.term A D I w (C.target b) y) (C.internalHom A D I (C.target b) y) p) :
    P.pathEvaluationTail b w x y p
      (f.comp (P.internalEvaluation (C.target b) y) (add_zero p)) =
    (C.prefixTailCochain A D I b w x y p f).comp (P.internalEvaluation x y) (add_zero p) := by
  rw [pathEvaluationTail, tensorLeftHom_cochain_comp, tensorLeftHom_cochain_comp,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← internalEvaluation_prefixPath,
    ← Cochain.comp_assoc_of_second_is_zero_cochain]
  rfl

lemma pathEvaluation_differential (w : List I) (x y : D) :
    δ 0 1 (P.pathEvaluation w x y) =
      (C.replaceRow A D I w x y).comp (P.internalEvaluation x y) (add_zero 1) := by
  induction w generalizing x with
  | nil => rw [pathEvaluation_nil, δ_ofHom, Family.replaceRow_nil, Cochain.zero_comp]
  | cons b w ih =>
    rw [pathEvaluation_cons_differential, ih (C.target b), pathEvaluationTail_internalEvaluation,
      Family.replaceRow_cons, Cochain.add_comp _ _ _ (add_zero 1),
      Cochain.comp_assoc_of_second_is_zero_cochain, internalEvaluation_precomp]

lemma internalEvaluation_differential (x y : D) :
    δ 0 1 (P.internalEvaluation x y) =
      (C.replacement A D I x y).comp (P.internalEvaluation x y) (add_zero 1) := by
  apply C.pathCochain_ext A D I x y 1
  intro w
  rw [← δ_ofHom_comp, internalEvaluation_precomp,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, Family.replacement_precomp]
  exact P.pathEvaluation_differential w x y

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
end

end EvaluationReplacement

/-! ## Evaluation（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/Evaluation.lean） -/

/-! # 指定原始元付きdg関手の最終cell Hom上の評価chain map

## 概要
指定原始元付きdg関手の最終cell Hom上の評価chain map。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section Evaluation
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {I : Type w} [Small.{u} I]
  {C : Family A D I} {E : Type z} [DGCategory A E] {F : DGFunctor A D E}
variable (P : PrimitiveData A D I C E F)

/-- 指定原始元を使う評価は、最終Hom微分についての実際のchain mapとなる。 -/
def attachedEvaluation (x y : D) :
    C.attachedHom A D I x y ⟶ homObject A E (F.obj x) (F.obj y) :=
  perturbSourceMap (C.internalHom A D I x y)
    (homObject A E (F.obj x) (F.obj y))
    (C.replacement A D I x y) (C.replacement_closed A D I x y) (C.replacement_square_zero A D I x y)
    (P.internalEvaluation x y) (P.internalEvaluation_differential x y)

lemma attachedEvaluation_f (x y : D) (i : ℤ) :
    (P.attachedEvaluation x y).f i = (P.internalEvaluation x y).v i i (add_zero i) := rfl

lemma attachedEvaluation_original (x y : D) :
    C.originalHomInclusion A D I x y ≫ P.attachedEvaluation x y = F.map x y := by
  apply HomologicalComplex.Hom.ext
  funext i
  rw [HomologicalComplex.comp_f, Family.originalHomInclusion_f, attachedEvaluation_f]
  have h := congrArg (fun f : Cochain (homObject A D x y)
      (homObject A E (F.obj x) (F.obj y)) 0 =>
    f.v i i (add_zero i)) (P.internalEvaluation_original x y)
  simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using h

lemma attachedEvaluation_generator (i : I) :
    (P.attachedEvaluation (C.source i) (C.target i)).f (C.degree i)
      (C.generatorElement A D I i) = P.primitive i := by
  have h := congrArg (fun f : Cochain (C.generator A D I i)
      (homObject A E (F.obj (C.source i)) (F.obj (C.target i))) 0 =>
    f.v (C.degree i) (C.degree i) (add_zero _)
      ((singleObjXSelf (.up ℤ) (C.degree i) (𝟙_ (ModuleCat.{u} A))).inv (1 : A)))
    (P.internalEvaluation_generator i)
  rw [cochain_ofHom_comp_apply, cochain_generator] at h
  exact h

lemma attachedEvaluation_path (w : List I) (x y : D) (i : ℤ) :
    (C.inclusion A D I w x y).f i ≫ (P.attachedEvaluation x y).f i =
      (P.pathEvaluation w x y).v i i (add_zero i) := by
  rw [attachedEvaluation_f]
  have h := congrArg (fun f : Cochain (C.term A D I w x y)
      (homObject A E (F.obj x) (F.obj y)) 0 =>
    f.v i i (add_zero i)) (P.internalEvaluation_precomp x y w)
  simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using h

lemma attachedEvaluation_unit (x : D) :
    C.attachedIdentity A D I x ≫ P.attachedEvaluation x x =
      eId (Complex A) (F.obj x) := by
  rw [Family.attachedIdentity, Category.assoc, attachedEvaluation_original, F.map_id]

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
end

end Evaluation

/-! ## EvaluationComposition（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/EvaluationComposition.lean） -/

/-! # 最終Homの評価chain mapの合成保存

## 概要
最終Homの評価chain mapの合成保存。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section EvaluationComposition
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {I : Type w} [Small.{u} I]
  {C : Family A D I} {E : Type z} [DGCategory A E] {F : DGFunctor A D E}
variable (P : PrimitiveData A D I C E F)

lemma attachedEvaluation_composition (x y z : D) :
    C.attachedComposition A D I x y z ≫ P.attachedEvaluation x z =
    (P.attachedEvaluation x y ⊗ₘ P.attachedEvaluation y z) ≫
      eComp (Complex A) (F.obj x) (F.obj y) (F.obj z) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply mapBifunctor.hom_ext
  intro p q hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a b
  change (P.attachedEvaluation x z).f n
      ((C.attachedComposition A D I x y z).f n
        (ιTensorObj (C.attachedHom A D I x y) (C.attachedHom A D I y z) p q n hn (a ⊗ₜ[A] b))) =
    (eComp (Complex A) (F.obj x) (F.obj y) (F.obj z)).f n
      ((P.attachedEvaluation x y ⊗ₘ P.attachedEvaluation y z).f n
        (ιTensorObj (C.attachedHom A D I x y) (C.attachedHom A D I y z) p q n hn (a ⊗ₜ[A] b)))
  rw [Family.attachedComposition_apply, tensorMap_apply]
  simp only [attachedEvaluation_f]
  have h := congrArg (fun f : Cochain (C.internalHom A D I x y ⊗ C.internalHom A D I y z)
      (homObject A E (F.obj x) (F.obj z)) 0 =>
    f.v n n (add_zero n)
      (ιTensorObj (C.internalHom A D I x y) (C.internalHom A D I y z) p q n hn (a ⊗ₜ[A] b)))
    (P.internalEvaluation_composition x y z)
  rw [cochain_ofHom_comp_apply, cochain_comp_ofHom_apply, tensorZeroCochain_apply] at h
  exact h

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
end

end EvaluationComposition

/-! ## Extension（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/Extension.lean） -/

/-! # 指定原始元を持つdg関手の任意次数cell付加への延長

## 概要
指定原始元を持つdg関手の任意次数cell付加への延長。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section Extension
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
open CategoryTheory HomologicalComplex
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {I : Type w} [Small.{u} I]
  {C : Family A D I} {E : Type z} [DGCategory A E] {F : DGFunctor A D E}
variable (P : PrimitiveData A D I C E F)

/-- 各生成cellを指定原始元へ送る主豊穣dg関手。 -/
def extension : DGFunctor A (C.Objects A D I) E where
  obj x := F.obj x.val
  map x y := P.attachedEvaluation x.val y.val
  map_id x := P.attachedEvaluation_unit x.val
  map_comp x y z := P.attachedEvaluation_composition x.val y.val z.val

lemma embedding_comp_extension : (C.embedding A D I).comp P.extension = F := by
  apply EnrichedFunctor.ext (Complex A)
    (F := (C.embedding A D I).comp P.extension) (G := F) (fun _ => rfl)
  intro x y
  change (C.originalHomInclusion A D I x y ≫ P.attachedEvaluation x y) ≫ eqToHom (by rfl) = _
  rw [eqToHom_refl, Category.comp_id, attachedEvaluation_original]

lemma extension_generator (i : I) :
    (P.extension.map (⟨C.source i⟩ : C.Objects A D I) ⟨C.target i⟩).f (C.degree i)
      (C.generatorElement A D I i) = P.primitive i := P.attachedEvaluation_generator i

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
end

end Extension

/-! ## Augmentation（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/Augmentation.lean） -/

/-! # 全境界cellの同時付加と指定原始元への増大

## 概要
全境界cellの同時付加と指定原始元への増大。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section Augmentation
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCategoryBoundaryCells
open CategoryTheory HomologicalComplex
open DGCellAttachment
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] (F : DGFunctor A D E)

/-- 全境界cellをその添字に保存された原始元へ送る実際の増大dg関手。 -/
def attachedAugmentation :
    DGFunctor A ((boundaryFamily A D E F).Objects A D (Index A D E F)) E :=
  (primitiveData A D E F).extension

lemma embedding_comp_attachedAugmentation :
    ((boundaryFamily A D E F).embedding A D (Index A D E F)).comp
      (attachedAugmentation A D E F) = F :=
  (primitiveData A D E F).embedding_comp_extension

/-- 元の各境界cellは次段のHomで埋まり、指定されたtarget原始元へ厳密に送られる。 -/
lemma attachedAugmentation_fills (x y : D) (c : ComplexBoundaryCell A (F.map x y)) :
    ∃ t : ((boundaryFamily A D E F).attachedHom A D (Index A D E F) x y).X c.degree,
      ((boundaryFamily A D E F).attachedHom A D (Index A D E F) x y).d
        c.degree (c.degree + 1) t =
        ((boundaryFamily A D E F).originalHomInclusion A D (Index A D E F) x y).f
          (c.degree + 1) c.cycle.val ∧
      ((attachedAugmentation A D E F).map ⟨x⟩ ⟨y⟩).f c.degree t = c.primitive := by
  let i : Index A D E F := ⟨x, y, c⟩
  refine ⟨(boundaryFamily A D E F).generatorElement A D (Index A D E F) i, ?_, ?_⟩
  · exact (boundaryFamily A D E F).differential_generatorElement A D (Index A D E F) i
  · exact (primitiveData A D E F).extension_generator i

end SerrePositivity.DifferentialGraded.DGCategoryBoundaryCells
end

end Augmentation

/-! ## RestrictionData（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/RestrictionData.lean） -/

/-! # cell付加からのdg関手を元の関手と指定原始元へ制限する

## 概要
cell付加からのdg関手を元の関手と指定原始元へ制限する。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section RestrictionData
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : Family A D I) {E : Type z} [DGCategory A E]

abbrev restrictFunctor (G : DGFunctor A (C.Objects A D I) E) : DGFunctor A D E :=
  (C.embedding A D I).comp G

def restrictPrimitives (G : DGFunctor A (C.Objects A D I) E) :
    PrimitiveData A D I C E (C.restrictFunctor A D I G) where
  primitive i := (G.map ⟨C.source i⟩ ⟨C.target i⟩).f (C.degree i) (C.generatorElement A D I i)
  boundary i := by
    have h := congrArg (fun f => f (C.generatorElement A D I i))
      ((G.map ⟨C.source i⟩ ⟨C.target i⟩).comm (C.degree i) (C.degree i + 1))
    change (homObject A E (G.obj ⟨C.source i⟩) (G.obj ⟨C.target i⟩)).d
      (C.degree i) (C.degree i + 1)
      ((G.map ⟨C.source i⟩ ⟨C.target i⟩).f (C.degree i) (C.generatorElement A D I i)) =
      (G.map ⟨C.source i⟩ ⟨C.target i⟩).f (C.degree i + 1)
        ((C.attachedHom A D I (C.source i) (C.target i)).d (C.degree i) (C.degree i + 1)
          (C.generatorElement A D I i)) at h
    rw [differential_generatorElement] at h
    exact h

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end RestrictionData

/-! ## Reconstruction（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/Reconstruction.lean） -/

/-! # cell付加からのdg関手を有限path評価で再構成する

## 概要
cell付加からのdg関手を有限path評価で再構成する。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section Reconstruction
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : Family A D I) {E : Type z} [DGCategory A E]

def restrictionHomCochain (G : DGFunctor A (C.Objects A D I) E) (x y : D) :
    Cochain (C.internalHom A D I x y) (homObject A E (G.obj ⟨x⟩) (G.obj ⟨y⟩)) 0 :=
  Cochain.ofHoms (fun n => (G.map ⟨x⟩ ⟨y⟩).f n)

lemma restrictionHomCochain_path (G : DGFunctor A (C.Objects A D I) E)
    (w : List I) (x y : D) :
    (Cochain.ofHom (C.inclusion A D I w x y)).comp
      (C.restrictionHomCochain A D I G x y) (zero_add 0) =
      (C.restrictPrimitives A D I G).pathEvaluation w x y := by
  induction w generalizing x with
  | nil =>
    apply Cochain.ext₀
    intro n
    simp only [PrimitiveData.pathEvaluation_nil, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
      restrictionHomCochain, Cochain.ofHoms_v]
    rfl
  | cons b w ih =>
    apply sphereMiddleCochain_ext₀ A (C.degree b)
    intro p q n hn a t
    have h := congrArg (fun v : (C.attachedHom A D I x y).X n => (G.map ⟨x⟩ ⟨y⟩).f n v)
      (C.path_inclusion_generator A D I b w x y p q (C.degree b + q) n rfl hn a t)
    rw [DGFunctor.map_forward A G (x := ⟨x⟩) (y := ⟨C.source b⟩) (z := ⟨y⟩),
      DGFunctor.map_forward A G (x := ⟨C.source b⟩) (y := ⟨C.target b⟩) (z := ⟨y⟩)] at h
    have ht := congrArg (fun f : Cochain (C.term A D I w (C.target b) y)
        (homObject A E (G.obj ⟨C.target b⟩) (G.obj ⟨y⟩)) 0 =>
      f.v q q (add_zero q) t) (ih (C.target b))
    rw [cochain_ofHom_comp_apply, restrictionHomCochain, Cochain.ofHoms_v] at ht
    have htail := congrArg (fun z : (homObject A E (G.obj ⟨C.target b⟩) (G.obj ⟨y⟩)).X q =>
      forward A
        ((G.map ⟨x⟩ ⟨C.source b⟩).f p ((C.originalHomInclusion A D I x (C.source b)).f p a))
        (forward A ((G.map ⟨C.source b⟩ ⟨C.target b⟩).f (C.degree b)
          (C.generatorElement A D I b)) z rfl) hn) ht
    let v : (C.term A D I (b :: w) x y).X n :=
      ιTensorObj (homObject A D x (C.source b))
        (C.generator A D I b ⊗ C.term A D I w (C.target b) y) p (C.degree b + q) n hn
        (a ⊗ₜ[A] ιTensorObj (C.generator A D I b) (C.term A D I w (C.target b) y)
          (C.degree b) q (C.degree b + q) rfl
          ((singleObjXSelf (.up ℤ) (C.degree b) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] t))
    have he := cochain_ofHom_comp_apply (C.inclusion A D I (b :: w) x y)
      (C.restrictionHomCochain A D I G x y) (add_zero n) v
    rw [restrictionHomCochain, Cochain.ofHoms_v] at he
    have hr := (C.restrictPrimitives A D I G).pathEvaluation_cons_generator
      b w x y p q (C.degree b + q) n rfl hn a t
    exact he.trans (h.trans (htail.trans hr.symm))

lemma restrictionHomCochain_eq_internalEvaluation (G : DGFunctor A (C.Objects A D I) E)
    (x y : D) :
    C.restrictionHomCochain A D I G x y =
      (C.restrictPrimitives A D I G).internalEvaluation x y := by
  apply C.pathCochain_ext A D I x y 0
  intro w
  rw [restrictionHomCochain_path, PrimitiveData.internalEvaluation_precomp]

lemma extension_restrict (G : DGFunctor A (C.Objects A D I) E) :
    (C.restrictPrimitives A D I G).extension = G := by
  apply EnrichedFunctor.ext (Complex A)
    (F := (C.restrictPrimitives A D I G).extension) (G := G) (fun _ => rfl)
  intro x y
  cases x with
  | mk x =>
    cases y with
    | mk y =>
      change (C.restrictPrimitives A D I G).attachedEvaluation x y ≫
        eqToHom (by rfl) = G.map ⟨x⟩ ⟨y⟩
      rw [eqToHom_refl, Category.comp_id]
      apply HomologicalComplex.Hom.ext
      funext n
      rw [PrimitiveData.attachedEvaluation_f]
      have h := congrArg (fun f : Cochain (C.internalHom A D I x y)
          (homObject A E (G.obj ⟨x⟩) (G.obj ⟨y⟩)) 0 => f.v n n (add_zero n))
        (C.restrictionHomCochain_eq_internalEvaluation A D I G x y).symm
      simpa only [restrictionHomCochain, Cochain.ofHoms_v] using h

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end Reconstruction

/-! ## Universal（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/Universal.lean） -/

/-! # 元のdg関手と指定生成cellの像による延長の一意性

## 概要
元のdg関手と指定生成cellの像による延長の一意性。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section Universal
universe u v w z

noncomputable section
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {I : Type w}
  {C : Family A D I} {E : Type z} [DGCategory A E]

lemma PrimitiveData.hext {F G : DGFunctor A D E}
    (P : PrimitiveData A D I C E F) (Q : PrimitiveData A D I C E G)
    (hF : F = G) (hp : HEq P.primitive Q.primitive) : HEq P Q := by
  cases hF
  apply heq_of_eq
  have hp' := eq_of_heq hp
  cases P
  cases Q
  cases hp'
  rfl

variable [Small.{u} I]

lemma PrimitiveData.extension_congr {F G : DGFunctor A D E}
    (P : PrimitiveData A D I C E F) (Q : PrimitiveData A D I C E G)
    (hF : F = G) (hp : HEq P.primitive Q.primitive) : P.extension = Q.extension := by
  have h := P.hext Q hF hp
  cases hF
  have he := eq_of_heq h
  cases he
  rfl

variable (A D I C)

lemma extension_unique {F : DGFunctor A D E} (P : PrimitiveData A D I C E F)
    (G : DGFunctor A (C.Objects A D I) E) (hF : C.restrictFunctor A D I G = F)
    (hp : HEq (C.restrictPrimitives A D I G).primitive P.primitive) : G = P.extension :=
  (C.extension_restrict A D I G).symm.trans
    ((C.restrictPrimitives A D I G).extension_congr P hF hp)

lemma functor_ext (G H : DGFunctor A (C.Objects A D I) E)
    (hF : C.restrictFunctor A D I G = C.restrictFunctor A D I H)
    (hp : HEq (C.restrictPrimitives A D I G).primitive
      (C.restrictPrimitives A D I H).primitive) : G = H :=
  (C.extension_restrict A D I G).symm.trans
    (((C.restrictPrimitives A D I G).extension_congr (C.restrictPrimitives A D I H) hF hp).trans
      (C.extension_restrict A D I H))

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end Universal
