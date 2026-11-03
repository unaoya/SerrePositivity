module

public import SerrePositivity.DifferentialGraded.Tensor.Fubini
public import SerrePositivity.DifferentialGraded.Module.Graded
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import SerrePositivity.DifferentialGraded.Tensor.Graded
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
public import SerrePositivity.DifferentialGraded.Category.Tensor
public import SerrePositivity.DifferentialGraded.Module.Disk
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
public import SerrePositivity.DifferentialGraded.Complexes.TensorShift
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct
public import SerrePositivity.DifferentialGraded.Module.ActionLimits
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHom.CoefficientClosure

/-!
# Module.FreeSphere

## 概要
9 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## FunctorExtension（旧 SerrePositivity/DifferentialGraded/Module/FunctorExtension.lean） -/

/-! # dg関手のgraph bimoduleによる加群延長

## 概要
Hom_E(e,Fd)を値とする右E・左D bimoduleを既存tensor合成へ入力する。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section FunctorExtension
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- dg関手のgraph。各D対象でE上の実際の代表右加群となる。 -/
def functorGraph : Bimodule A E D := F.comp (dgYoneda A E)

omit [Small.{u} D] in
lemma functorGraph_value (e : E) (d : D) :
    (functorGraph A D E F).value e d = homObject A E e (F.obj d) := rfl

/-- graphとのtensorによる右dg加群の延長。全加群型のsmallnessは不要。 -/
def dgModuleExtension : DGFunctor A (RightModule A D) (RightModule A E) :=
  (BimoduleTensor.compose A E D (RightModule A D) (functorGraph A D E F)
    (DGFunctor.id (RightModule A D))).toFunctor

lemma dgModuleExtension_value (M : RightModule A D) (e : E) :
    ((dgModuleExtension A D E F).obj M).obj (op e) =
      BalancedTensor.obj A D M ((functorGraph A D E F).leftAt e) := rfl

/-- 代表加群の延長は対応するEの代表加群。Hom flatness仮定は不要。 -/
def dgModuleExtensionRepresentableIso (d : D) :
    ForgetEnrichment.of (Complex A) ((dgModuleExtension A D E F).obj (representable A d)) ≅
      ForgetEnrichment.of (Complex A) (representable A (F.obj d)) :=
  BimoduleTensor.rightUnitIso A E D (functorGraph A D E F) d

end SerrePositivity.DifferentialGraded
end

end FunctorExtension

/-! ## FunctorExtensionMaps（旧 SerrePositivity/DifferentialGraded/Module/FunctorExtensionMaps.lean） -/

/-! # graph延長の閉零射とtensor生成元上の計算

## 概要
graph延長の閉零射とtensor生成元上の計算。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section FunctorExtensionMaps
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

lemma dgModuleExtension_map_π (M N : RightModule A D) (e : E) :
    (dgModuleExtension A D E F).map M N ≫
      moduleHomπ A E ((dgModuleExtension A D E F).obj M)
        ((dgModuleExtension A D E F).obj N) e =
      BalancedTensor.rightHomMap A D M N ((functorGraph A D E F).leftAt e) := by
  have h := BimoduleTensor.compose_leftMap_π A E D (RightModule A D) (functorGraph A D E F)
      (DGFunctor.id (RightModule A D)) M N e
  change (dgModuleExtension A D E F).map M N ≫
    moduleHomπ A E ((dgModuleExtension A D E F).obj M)
      ((dgModuleExtension A D E F).obj N) e =
    𝟙 _ ≫ BalancedTensor.rightHomMap A D M N ((functorGraph A D E F).leftAt e) at h
  exact h.trans (Category.id_comp _)

lemma dgModuleExtension_map_eval {M N : ModuleCategory A D} (f : M ⟶ N) (e : E) :
    (moduleEvaluation A E e).map ((dgModuleExtension A D E F).onClosed.map f) =
      BalancedTensor.rightTensorMap A D ((functorGraph A D E F).leftAt e) f := by
  apply Cochain.ofHom_injective
  rw [moduleEvaluation_cochain]
  change (moduleHomπ A E _ _ e).f 0
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f ≫
      (dgModuleExtension A D E F).map _ _)).val = _
  rw [cycleFromUnit_postcomp]
  have h := congrArg (fun k => k.f 0 (cycleFromUnit _
    (ForgetEnrichment.homTo (Complex A) f)).val)
      (dgModuleExtension_map_π A D E F (ForgetEnrichment.to (Complex A) M)
        (ForgetEnrichment.to (Complex A) N) e)
  exact h.trans (BalancedTensor.rightHomMap_closedElement A D
    ((functorGraph A D E F).leftAt e) f)

lemma dgModuleExtension_map_eval_element {M N : ModuleCategory A D} (f : M ⟶ N)
    (e : E) (d : D) {r s n : ℤ}
    (m : ((ForgetEnrichment.to (Complex A) M).obj (op d)).X r)
    (h : GradedHom A e (F.obj d) s) (hn : r + s = n) :
    ((moduleEvaluation A E e).map ((dgModuleExtension A D E F).onClosed.map f)).f n
      (BalancedTensor.element A D (ForgetEnrichment.to (Complex A) M)
        ((functorGraph A D E F).leftAt e) d m h hn) =
      BalancedTensor.element A D (ForgetEnrichment.to (Complex A) N)
        ((functorGraph A D E F).leftAt e) d (((moduleEvaluation A D d).map f).f r m) h hn := by
  have he := congrArg (fun k => k.f n
    (BalancedTensor.element A D (ForgetEnrichment.to (Complex A) M)
      ((functorGraph A D E F).leftAt e) d m h hn)) (dgModuleExtension_map_eval A D E F f e)
  exact he.trans (BalancedTensor.rightTensorMap_element A D
    ((functorGraph A D E F).leftAt e) f d m h hn)

end SerrePositivity.DifferentialGraded
end

end FunctorExtensionMaps

/-! ## RingComplexFunctor（旧 SerrePositivity/DifferentialGraded/Module/RingComplexFunctor.lean） -/

/-! # 通常の非有界複体から実際の一対象Aの右dg加群への関手 -/

@[expose] public section RingComplexFunctor
universe u

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A]

/-- 通常のchain mapを閉零射へ戻して、実際のringConstantDGを適用する。 -/
def complexToRingModule : Complex A ⥤ ModuleCategory A PUnit.{1} :=
  ForgetEnrichment.equivInverse (Complex A) (Complex A) ⋙ (ringConstantDG A).onClosed

instance complexToRingModuleAdditive : (complexToRingModule A).Additive := by
  let e : ClosedCategory A (Complex A) ≌ Complex A := ForgetEnrichment.equiv (Complex A)
  have : e.functor.Additive := closedToComplexAdditive (A := A)
  have : (ForgetEnrichment.equivInverse (Complex A) (Complex A)).Additive :=
    show e.inverse.Additive from inferInstance
  dsimp [complexToRingModule]
  infer_instance

end SerrePositivity.DifferentialGraded
end

end RingComplexFunctor

/-! ## FreeSphereClosedLinear（旧 SerrePositivity/DifferentialGraded/Module/FreeSphereClosedLinear.lean） -/

/-!
概要：全整数次数の自由 sphere からの実閉射と評価 cycle の同値の線形性を公開する。
方針：恒等射の cycle に対する既存の後合成自然性から加法・スカラー作用を回収する。
規約：元の freeSphereHomEquiv を変更しない。
使われ方：c′ の任意シフト自由入力から直和への有限係数表示。
-/

@[expose] public section FreeSphereClosedLinear
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma freeSphereHomEquiv_val (x : D) (n : ℤ) (M : ModuleCategory R D)
    (f : freeSphere R D x n ⟶ M) :
    (freeSphereHomEquiv R D x n M f).val =
      ((moduleEvaluation R D x).map f).f n
        (freeSphereHomEquiv R D x n (freeSphere R D x n) (𝟙 _)).val := by
  simpa only [Category.id_comp] using
    freeSphereHomEquiv_naturality_val R D x n (𝟙 (freeSphere R D x n)) f

def freeSphereClosedCycleLinearEquiv (x : D) (n : ℤ) (M : ModuleCategory R D) :
    (freeSphere R D x n ⟶ M) ≃ₗ[R]
      complexCycles R ((moduleEvaluation R D x).obj M) n where
  toEquiv := freeSphereHomEquiv R D x n M
  map_add' f g := by
    apply Subtype.ext
    change (freeSphereHomEquiv R D x n M (f + g)).val =
      (freeSphereHomEquiv R D x n M f).val + (freeSphereHomEquiv R D x n M g).val
    rw [freeSphereHomEquiv_val R D x n M (f + g),
      freeSphereHomEquiv_val R D x n M f, freeSphereHomEquiv_val R D x n M g]
    rw [Functor.map_add]
    rfl
  map_smul' r f := by
    apply Subtype.ext
    change (freeSphereHomEquiv R D x n M (r • f)).val =
      r • (freeSphereHomEquiv R D x n M f).val
    rw [freeSphereHomEquiv_val R D x n M (r • f), freeSphereHomEquiv_val R D x n M f]
    letI : (moduleEvaluation R D x).Linear R := by
      dsimp [moduleEvaluation]
      infer_instance
    rw [Functor.map_smul]
    rfl

end SerrePositivity.DifferentialGraded
end

end FreeSphereClosedLinear

/-! ## FreeSphereClosedCoefficient（旧 SerrePositivity/DifferentialGraded/Module/FreeSphereClosedCoefficient.lean） -/

/-!
概要：二つの任意整数次数の自由 sphere 間閉射を、元の dg Hom の斉次係数で検出する。
方針：自由 sphere の cycle 評価と sphere tensor shift 同型を合成する。
規約：次数 n から次数 m の自由生成元への閉射は Hom の次数 n-m で読む。
使われ方：c′ の行有限自由閉射行列を元の dg 圏のκ係数へ戻す。
-/

@[expose] public section FreeSphereClosedCoefficient
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

def freeSphereClosedCoefficient (x y : D) (n m : ℤ)
    (f : freeSphere R D x n ⟶ freeSphere R D y m) : GradedHom R x y (n - m) :=
  (complexSphereTensorShiftIso R m (homObject R D x y)).hom.f n
    (freeSphereHomEquiv R D x n (freeSphere R D y m) f).val

lemma freeSphereClosedCoefficient_injective (x y : D) (n m : ℤ) :
    Function.Injective (freeSphereClosedCoefficient R D x y n m) := by
  intro f g h
  apply (freeSphereHomEquiv R D x n (freeSphere R D y m)).injective
  apply Subtype.ext
  exact (ModuleCat.mono_iff_injective
    ((complexSphereTensorShiftIso R m (homObject R D x y)).hom.f n)).mp inferInstance h

def freeSphereClosedCoefficientLinearMap (x y : D) (n m : ℤ) :
    (freeSphere R D x n ⟶ freeSphere R D y m) →ₗ[R] GradedHom R x y (n - m) :=
  ((complexSphereTensorShiftIso R m (homObject R D x y)).hom.f n).hom.comp
    (((complexCycles R ((moduleEvaluation R D x).obj (freeSphere R D y m)) n).subtype).comp
      (freeSphereClosedCycleLinearEquiv R D x n (freeSphere R D y m)).toLinearMap)

end SerrePositivity.DifferentialGraded
end

end FreeSphereClosedCoefficient

/-! ## FreeSphereClosedCoefficientCycles（旧 SerrePositivity/DifferentialGraded/Module/FreeSphereClosedCoefficientCycles.lean） -/

/-!
概要：任意シフト自由 sphere 間の閉射を、元の Hom の閉斉次係数と線形に同定する。
方針：自由 sphere の cycle 表示、tensor shift、shift cycle の符号除去を合成する。
規約：次数 n-m の元の係数を保持し、同じ閉射を逆構成で回収する。
使われ方：c′ のκ係数コードから自由行列閉射を持ち上げる。
-/

@[expose] public section FreeSphereClosedCoefficientCycles
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

def freeSphereClosedCoefficientCycleEquiv (x y : D) (n m : ℤ) :
    (freeSphere R D x n ⟶ freeSphere R D y m) ≃ₗ[R]
      complexCycles R (homObject R D x y) (n - m) :=
  (freeSphereClosedCycleLinearEquiv R D x n (freeSphere R D y m)).trans
    ((complexCycleIso R (complexSphereTensorShiftIso R m (homObject R D x y)) n).trans
      (complexShiftCycleIso R (homObject R D x y) (-m) n))

lemma freeSphereClosedCoefficientCycleEquiv_val (x y : D) (n m : ℤ)
    (f : freeSphere R D x n ⟶ freeSphere R D y m) :
    (freeSphereClosedCoefficientCycleEquiv R D x y n m f).val =
      freeSphereClosedCoefficient R D x y n m f := rfl

lemma freeSphereClosedCoefficient_closed (x y : D) (n m : ℤ)
    (f : freeSphere R D x n ⟶ freeSphere R D y m) :
    (homObject R D x y).d (n - m) (n - m + 1)
      (freeSphereClosedCoefficient R D x y n m f) = 0 :=
  (freeSphereClosedCoefficientCycleEquiv R D x y n m f).property

def freeSphereClosedCoefficientPreimage (x y : D) (n m : ℤ)
    (z : complexCycles R (homObject R D x y) (n - m)) :
    freeSphere R D x n ⟶ freeSphere R D y m :=
  (freeSphereClosedCoefficientCycleEquiv R D x y n m).symm z

lemma freeSphereClosedCoefficientPreimage_coefficient (x y : D) (n m : ℤ)
    (z : complexCycles R (homObject R D x y) (n - m)) :
    freeSphereClosedCoefficient R D x y n m
      (freeSphereClosedCoefficientPreimage R D x y n m z) = z.val :=
  congrArg Subtype.val ((freeSphereClosedCoefficientCycleEquiv R D x y n m).apply_symm_apply z)

end SerrePositivity.DifferentialGraded
end

end FreeSphereClosedCoefficientCycles

/-! ## FreeSphereClosedCoproductSupport（旧 SerrePositivity/DifferentialGraded/Module/FreeSphereClosedCoproductSupport.lean） -/

/-!
概要：任意整数次数の自由 sphere から直和への実閉射を、有限個の閉射の和として表示する。
方針：実自由 sphere の次数 n の cycle に余積の有限 support 表示を適用し、閉射へ戻す。
規約：ホモトピー同値ではなく、元の閉射そのものの等式を得る。
使われ方：c′ の全シフト自由入力の閉射を有限係数族へ分解する第一段階。
-/

@[expose] public section FreeSphereClosedCoproductSupport
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma moduleFreeSphereClosedCoproduct_rep {J : Type u} (x : D) (n : ℤ)
    (M : J → ModuleCategory R D)
    (f : freeSphere R D x n ⟶ ∐ M) :
    ∃ (t : Finset J)
      (g : ∀ j, freeSphere R D x n ⟶ M j),
      ∑ j ∈ t, g j ≫ Sigma.ι M j = f := by
  classical
  let E := moduleEvaluation R D x
  let s : Cofan (fun j => E.obj (M j)) :=
    Cofan.mk (E.obj (∐ M)) (fun j => E.map (Sigma.ι M j))
  have hs : IsColimit s := isColimitCofanMkObjOfIsColimit E M _ (coproductIsCoproduct M)
  obtain ⟨t, z, hz⟩ := complexCofan_cycle_rep R (fun j => E.obj (M j)) s hs n
    (freeSphereHomEquiv R D x n (∐ M) f)
  let g := fun j => (freeSphereHomEquiv R D x n (M j)).symm (z j)
  refine ⟨t, g, ?_⟩
  apply (freeSphereHomEquiv R D x n (∐ M)).injective
  apply Subtype.ext
  calc
    _ = ∑ j ∈ t, (freeSphereHomEquiv R D x n (∐ M)
        (g j ≫ Sigma.ι M j)).val := by
      have h := map_sum (freeSphereClosedCycleLinearEquiv R D x n (∐ M)).toLinearMap
        (fun j => g j ≫ Sigma.ι M j) t
      change freeSphereHomEquiv R D x n (∐ M) (∑ j ∈ t, g j ≫ Sigma.ι M j) =
        ∑ j ∈ t, freeSphereHomEquiv R D x n (∐ M) (g j ≫ Sigma.ι M j) at h
      simpa only [Submodule.coe_sum] using congrArg Subtype.val h
    _ = ∑ j ∈ t, (s.inj j).f n (z j).val := by
      apply Finset.sum_congr rfl
      intro j _
      rw [freeSphereHomEquiv_naturality_val]
      change (s.inj j).f n
        ((freeSphereHomEquiv R D x n (M j))
          ((freeSphereHomEquiv R D x n (M j)).symm (z j))).val = _
      rw [Equiv.apply_symm_apply]
    _ = _ := hz

end SerrePositivity.DifferentialGraded
end

end FreeSphereClosedCoproductSupport

/-! ## FreeSphereCoproductClosedMatrix（旧 SerrePositivity/DifferentialGraded/Module/FreeSphereCoproductClosedMatrix.lean） -/

/-!
概要：全整数シフトの自由 sphere の直和間の実閉射を、κ個以下の行有限係数から回収する。
方針：各自由 sphere の閉射の有限 support を選択し、余積の普遍性で元の全射を同定する。
規約：係数は自由 sphere 間の実閉射で、元の Hom 複体への係数抽出は別工程。
使われ方：c′ の全シフト自由直和における有限係数化。
-/

@[expose] public section FreeSphereCoproductClosedMatrix
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma moduleFreeSphereCoproduct_closed_matrix {I J : Type u}
    (x : I → D) (n : I → ℤ) (y : J → D) (m : J → ℤ)
    (f : (∐ fun i => freeSphere R D (x i) (n i)) ⟶ ∐ fun j => freeSphere R D (y j) (m j))
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) (hI : Cardinal.mk I ≤ κ) :
    ∃ (support : I → Finset J)
      (coefficient : ∀ i j, freeSphere R D (x i) (n i) ⟶ freeSphere R D (y j) (m j)),
      (Sigma.desc (fun i => ∑ j ∈ support i,
        coefficient i j ≫ Sigma.ι (fun j => freeSphere R D (y j) (m j)) j) = f) ∧
      Cardinal.mk (Σ i, (support i : Set J)) ≤ κ := by
  classical
  choose support coefficient hrow using (fun i => moduleFreeSphereClosedCoproduct_rep
    R D (x i) (n i) (fun j => freeSphere R D (y j) (m j))
    (Sigma.ι (fun i => freeSphere R D (x i) (n i)) i ≫ f))
  refine ⟨support, coefficient, ?_, finiteRowCoefficientIndex_cardinal_le support κ hκ hI⟩
  apply Sigma.hom_ext
  intro i
  rw [Sigma.ι_desc]
  exact hrow i

end SerrePositivity.DifferentialGraded
end

end FreeSphereCoproductClosedMatrix

/-! ## RestrictionRepresentable（旧 SerrePositivity/DifferentialGraded/Module/RestrictionRepresentable.lean） -/

/-! # dg関手のHom写像による代表加群と制限代表加群の比較

## 概要
dg関手のHom写像による代表加群と制限代表加群の比較。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section RestrictionRepresentable
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

omit [Small.{u} D] [Small.{u} E] in
lemma representableRestriction_naturality (d : D) (x y : Dᵒᵖ) :
    (representable A d).map x y ≫
      homPostcompose ((representable A d).obj x) (F.map y.unop d) =
    (restrictModule A D E F.op (representable A (F.obj d))).map x y ≫
      homPrecompose (F.map x.unop d) ((representable A (F.obj d)).obj (F.op.obj y)) := by
  apply hom_naturality_of_apply
  intro p f
  apply Cochain.ext
  intro r n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro h
  rw [Cochain.comp_zero_cochain_v _ _ r n hn,
    Cochain.zero_cochain_comp_v _ _ r n hn]
  change (F.map y.unop d).f n
    (((representableMap A d x y).f p f).v r n hn h) =
    (((representableMap A (F.obj d) (F.op.obj x) (F.op.obj y)).f p
      ((F.map y.unop x.unop).f p f)).v r n hn ((F.map x.unop d).f r h))
  rw [representableMap_apply, representableMap_apply]
  exact F.map_forward A f h (by omega)

/-- 各成分がFのHom chain mapである全Hom自然な閉零比較。 -/
def representableRestrictionMap (d : D) :
    ForgetEnrichment.of (Complex A) (representable A d) ⟶
      (moduleRestriction A D E F.op).obj
        (ForgetEnrichment.of (Complex A) (representable A (F.obj d))) :=
  moduleMorphismMk A D (fun x => F.map x.unop d)
    (representableRestriction_naturality A D E F d)

lemma representableRestrictionMap_eval (d x : D) :
    (moduleEvaluation A D x).map (representableRestrictionMap A D E F d) = F.map x d :=
  moduleMorphismMk_eval A D _ _ x

lemma representableRestrictionMap_quasiIso (hF : HomQuasiIso F) (d : D) :
    moduleQuasiIso A D (representableRestrictionMap A D E F d) := by
  intro x
  rw [representableRestrictionMap_eval]
  exact hF x d

end SerrePositivity.DifferentialGraded
end

end RestrictionRepresentable
