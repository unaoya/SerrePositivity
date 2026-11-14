module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
public import SerrePositivity.DifferentialGraded.Complexes.TensorShift
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import SerrePositivity.DifferentialGraded.Perfect.RepresentableHomology
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct
public import SerrePositivity.DifferentialGraded.Module.ActionLimits
public import SerrePositivity.DifferentialGraded.Module.FreeSphere
public import SerrePositivity.DifferentialGraded.Module.Hom.ColimitsAndRightHom
public import SerrePositivity.DifferentialGraded.Module.TensorFree
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
public import SerrePositivity.DifferentialGraded.Module.Graded
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHom.CoefficientClosure
public import SerrePositivity.DifferentialGraded.Endomorphism.Module
public import SerrePositivity.DifferentialGraded.Tensor.BalancedElements
public import SerrePositivity.DifferentialGraded.Tensor.Parameter
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.Actions
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Module.Functor

## 概要
20 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## RingProjective（旧 SerrePositivity/DifferentialGraded/Module/RingProjective.lean） -/

/-! # 一対象A上の主Homによる射影性と通常のK-projective性 -/

@[expose] public section RingProjective
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A]

/-- 一対象AではHom endの射影性と評価複体のK-projective性が一致する。 -/
lemma ringModule_homotopicallyProjective_iff (M : RightModule A PUnit.{1}) :
    moduleHomotopicallyProjective A PUnit.{1} (ForgetEnrichment.of (Complex A) M) ↔
      (M.obj (op PUnit.unit)).IsKProjective := by
  constructor
  · intro hM
    apply isKProjective_of_homComplex_acyclic A
    intro N hN
    have h := hM (ForgetEnrichment.of (Complex A) (ringModule A N)) (fun _ => hN)
    exact cochainAcyclic_of_iso h (ringModuleHomIso A M (ringModule A N))
  · intro hM N hN
    let := hM
    exact cochainAcyclic_of_iso
      (homComplex_acyclic_of_isKProjective A (M.obj (op PUnit.unit))
        ((ForgetEnrichment.to (Complex A) N).obj (op PUnit.unit)) (hN PUnit.unit))
      (ringModuleHomIso A M (ForgetEnrichment.to (Complex A) N)).symm

end SerrePositivity.DifferentialGraded
end

end RingProjective

/-! ## RepresentableClosedCycles（旧 SerrePositivity/DifferentialGraded/Module/RepresentableClosedCycles.lean） -/

/-!
概要：代表加群からの実閉射を、対象での零 cycle と線形に同定する。
方針：全次数 Yoneda 同型を単位複体からの射に適用する。
規約：導来圏やホモトピー商を通さず、閉射そのものと後合成を保持する。
使われ方：c′ の自由代表から余積への閉射の有限係数表示。
-/

@[expose] public section RepresentableClosedCycles
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

def representableClosedCycleEquiv (x : D) (M : ModuleCategory R D) :
    (ForgetEnrichment.of (Complex R) (representable R x) ⟶ M) ≃
      zeroCycles ((ForgetEnrichment.to (Complex R) M).obj (op x)) where
  toFun f := cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f ≫
    (dgYonedaIso R x (ForgetEnrichment.to (Complex R) M)).hom)
  invFun z := ForgetEnrichment.homOf (Complex R) (unitFromCycle _ z ≫
    (dgYonedaIso R x (ForgetEnrichment.to (Complex R) M)).inv)
  left_inv f := by
    change unitFromCycle _ (cycleFromUnit _ _) ≫ _ = ForgetEnrichment.homTo (Complex R) f
    rw [unitFromCycle_cycleFromUnit, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  right_inv z := by
    change cycleFromUnit _ ((unitFromCycle _ z ≫ _) ≫ _) = z
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, cycleFromUnit_unitFromCycle]

def representableClosedCycleLinearEquiv (x : D) (M : ModuleCategory R D) :
    (ForgetEnrichment.of (Complex R) (representable R x) ⟶ M) ≃ₗ[R]
      zeroCycles ((ForgetEnrichment.to (Complex R) M).obj (op x)) where
  toEquiv := representableClosedCycleEquiv R D x M
  map_add' f g := by
    apply Subtype.ext
    change (dgYonedaIso R x (ForgetEnrichment.to (Complex R) M)).hom.f 0
      ((cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f)).val +
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) g)).val) = _
    exact map_add _ _ _
  map_smul' r f := by
    apply Subtype.ext
    change (dgYonedaIso R x (ForgetEnrichment.to (Complex R) M)).hom.f 0
      (r • (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f)).val) = _
    exact map_smul _ _ _

lemma representableClosedCycleEquiv_postcompose (x : D) {M N : ModuleCategory R D}
    (f : ForgetEnrichment.of (Complex R) (representable R x) ⟶ M) (g : M ⟶ N) :
    (representableClosedCycleEquiv R D x N (f ≫ g)).val =
      ((moduleEvaluation R D x).map g).f 0
        (representableClosedCycleEquiv R D x M f).val := by
  change (dgYonedaIso R x (ForgetEnrichment.to (Complex R) N)).hom.f 0
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (f ≫ g))).val = _
  rw [← moduleHomCycle_postcompose R D f g]
  exact congrArg (fun k => k.f 0
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f)).val)
    (dgYonedaIso_postcompose R D x g)

end SerrePositivity.DifferentialGraded
end

end RepresentableClosedCycles

/-! ## RepresentableClosedCoproductSupport（旧 SerrePositivity/DifferentialGraded/Module/RepresentableClosedCoproductSupport.lean） -/

/-!
概要：代表加群から任意直和への実閉射を、有限個の閉射の和として表示する。
方針：実 Yoneda の零 cycle に余積の有限 support 表示を適用し、閉射へ戻す。
規約：ホモトピー同値ではなく、元の閉射そのものの等式を得る。
使われ方：c′ の自由入力の閉射を有限係数族へ分解する第一段階。
-/

@[expose] public section RepresentableClosedCoproductSupport
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma moduleRepresentableClosedCoproduct_rep {J : Type u} (x : D)
    (M : J → ModuleCategory R D)
    (f : ForgetEnrichment.of (Complex R) (representable R x) ⟶ ∐ M) :
    ∃ (t : Finset J)
      (g : ∀ j, ForgetEnrichment.of (Complex R) (representable R x) ⟶ M j),
      ∑ j ∈ t, g j ≫ Sigma.ι M j = f := by
  classical
  let E := moduleEvaluation R D x
  let s : Cofan (fun j => E.obj (M j)) :=
    Cofan.mk (E.obj (∐ M)) (fun j => E.map (Sigma.ι M j))
  have hs : IsColimit s := isColimitCofanMkObjOfIsColimit E M _ (coproductIsCoproduct M)
  obtain ⟨t, z, hz⟩ := complexCofan_cycle_rep R (fun j => E.obj (M j)) s hs 0
    (representableClosedCycleEquiv R D x (∐ M) f)
  let g := fun j => (representableClosedCycleEquiv R D x (M j)).symm (z j)
  refine ⟨t, g, ?_⟩
  apply (representableClosedCycleEquiv R D x (∐ M)).injective
  apply Subtype.ext
  calc
    _ = ∑ j ∈ t, (representableClosedCycleEquiv R D x (∐ M)
        (g j ≫ Sigma.ι M j)).val := by
      have h := map_sum (representableClosedCycleLinearEquiv R D x (∐ M)).toLinearMap
        (fun j => g j ≫ Sigma.ι M j) t
      change representableClosedCycleEquiv R D x (∐ M) (∑ j ∈ t, g j ≫ Sigma.ι M j) =
        ∑ j ∈ t, representableClosedCycleEquiv R D x (∐ M) (g j ≫ Sigma.ι M j) at h
      simpa only [Submodule.coe_sum] using congrArg Subtype.val h
    _ = ∑ j ∈ t, (s.inj j).f 0 (z j).val := by
      apply Finset.sum_congr rfl
      intro j _
      rw [representableClosedCycleEquiv_postcompose]
      change (s.inj j).f 0
        ((representableClosedCycleEquiv R D x (M j))
          ((representableClosedCycleEquiv R D x (M j)).symm (z j))).val = _
      rw [Equiv.apply_symm_apply]
    _ = _ := hz

end SerrePositivity.DifferentialGraded
end

end RepresentableClosedCoproductSupport

/-! ## FreeRestrictionComparison（旧 SerrePositivity/DifferentialGraded/Module/FreeRestrictionComparison.lean） -/

/-!
概要：自由加群から制限した自由加群への、元の dg 関手の Hom 作用による閉射を構成する。
方針：代表加群の制限比較を左 tensor し、同じ成分を実閉射に束ねる。
規約：各成分を恒等 tensor と元の Hom 鎖写像に厳密に固定する。
使われ方：c′ の自由加群延長比較を閉射の全 Hom 係数と照合する。
-/

@[expose] public section FreeRestrictionComparison
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R D E)

def freeRestrictionComparison (y : D) (K : Complex R) :
    (freeAt y).obj K ⟶ (moduleRestriction R D E F.op).obj ((freeAt (F.obj y)).obj K) :=
  moduleMorphismMk R D
    (M := freeModule y K)
    (N := restrictModule R D E F.op (freeModule (F.obj y) K))
    (fun x => 𝟙 K ⊗ₘ F.map x.unop y) (by
    intro x z
    have h := tensorModuleFamilyMap_naturality R D K
      (M := representable R y)
      (N := restrictModule R D E F.op (representable R (F.obj y)))
      (fun x => F.map x.unop y) (representableRestriction_naturality R D E F y) x z
    dsimp only [freeModule, restrictModule, tensorModule, RightModule.map, RightModule.obj, RightModule.toFunctor,
      DGFunctor.comp, EnrichedFunctor.comp] at h ⊢
    simpa only [Category.assoc] using h)

lemma freeRestrictionComparison_eval (y x : D) (K : Complex R) :
    (moduleEvaluation R D x).map (freeRestrictionComparison R D E F y K) = 𝟙 K ⊗ₘ F.map x y :=
  moduleMorphismMk_eval R D _ _ x

lemma freeRestrictionComparison_freeHomEquiv (y : D) (K : Complex R) :
    freeHomEquiv R D y K ((moduleRestriction R D E F.op).obj ((freeAt (F.obj y)).obj K))
      (freeRestrictionComparison R D E F y K) =
    freeHomEquiv R E (F.obj y) K ((freeAt (F.obj y)).obj K) (𝟙 _) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  have hD := freeHomEquiv_apply R D y K
    ((moduleRestriction R D E F.op).obj ((freeAt (F.obj y)).obj K))
    (freeRestrictionComparison R D E F y K) n t
  have hE := freeHomEquiv_apply R E (F.obj y) K ((freeAt (F.obj y)).obj K) (𝟙 _) n t
  refine hD.trans (Eq.trans ?_ hE.symm)
  change @Eq ((K ⊗ homObject R E (F.obj y) (F.obj y)).X n) _ _
  rw [freeRestrictionComparison_eval, CategoryTheory.Functor.map_id]
  have hT := tensorMap_apply (𝟙 K) (F.map y y) n 0 n (add_zero n) t (unitElement R y).val
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply, F.map_unitElement R] at hT
  exact hT


end SerrePositivity.DifferentialGraded
end

end FreeRestrictionComparison

/-! ## RepresentableCoproductClosedMatrix（旧 SerrePositivity/DifferentialGraded/Module/RepresentableCoproductClosedMatrix.lean） -/

/-!
概要：代表加群の直和間の実閉射を、κ個以下の元の閉射からなる行有限行列で表示する。
方針：各包含からの閉射を有限 support へ分解し、Yoneda の全 Hom 同型で係数を戻す。
規約：各行の閉射等式を保持し、列数や係数環の基数は制限しない。
使われ方：c′ の自由直和閉射の係数精密化。シフトと一般 cell の場合は別工程。
-/

@[expose] public section RepresentableCoproductClosedMatrix
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma moduleRepresentableCoproduct_closed_matrix {I J : Type u}
    (x : I → D) (y : J → D)
    (f : (∐ fun i => ForgetEnrichment.of (Complex R) (representable R (x i))) ⟶
      ∐ fun j => ForgetEnrichment.of (Complex R) (representable R (y j)))
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) (hI : Cardinal.mk I ≤ κ) :
    ∃ (support : I → Finset J)
      (coefficient : ∀ i j, ForgetEnrichment.of (Complex R) (x i) ⟶
        ForgetEnrichment.of (Complex R) (y j)),
      (∀ i, ∑ j ∈ support i, (dgYoneda R D).onClosed.map (coefficient i j) ≫
        Sigma.ι (fun j => ForgetEnrichment.of (Complex R) (representable R (y j))) j =
        Sigma.ι (fun i => ForgetEnrichment.of (Complex R) (representable R (x i))) i ≫ f) ∧
      Cardinal.mk (Σ i, (support i : Set J)) ≤ κ := by
  classical
  choose support row hrow using (fun i => moduleRepresentableClosedCoproduct_rep R D (x i)
    (fun j => ForgetEnrichment.of (Complex R) (representable R (y j)))
    (Sigma.ι (fun i => ForgetEnrichment.of (Complex R) (representable R (x i))) i ≫ f))
  let coefficient := fun i j => dgYonedaClosedPreimage R D (row i j)
  refine ⟨support, coefficient, ?_, finiteRowCoefficientIndex_cardinal_le support κ hκ hI⟩
  intro i
  simpa only [coefficient, dgYonedaClosedPreimage_map] using hrow i

end SerrePositivity.DifferentialGraded
end

end RepresentableCoproductClosedMatrix

/-! ## FunctorGraphActions（旧 SerrePositivity/DifferentialGraded/Module/FunctorGraphActions.lean） -/

/-! # graphの左作用と共変representableの制限の一致

## 概要
U14のYoneda成分比較を再利用し、graph tensorの作用と制限の向きを固定する。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section FunctorGraphActions
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

omit [Small.{u} D] in
lemma functorGraph_leftAt (e : E) :
    (functorGraph A D E F).leftAt e = F.comp (leftRepresentable A e) := by
  apply EnrichedFunctor.ext (Complex A)
    (F := (functorGraph A D E F).leftAt e) (G := F.comp (leftRepresentable A e)) (fun _ => rfl)
  intro d d'
  change ((F.map d d' ≫ yonedaHom A E (F.obj d) (F.obj d')) ≫
    moduleHomπ A E (representable A (F.obj d)) (representable A (F.obj d')) e) ≫
      eqToHom (by rfl) = F.map d d' ≫ (leftRepresentable A e).map (F.obj d) (F.obj d')
  rw [eqToHom_refl, Category.comp_id, Category.assoc, yonedaHom_π, endomorphismYonedaApp]

/-- 延長の各値は、共変representableをFに沿って制限した左加群とのtensor。 -/
def dgModuleExtensionValueIso (M : RightModule A D) (e : E) :
    ((dgModuleExtension A D E F).obj M).obj (op e) ≅
      BalancedTensor.obj A D M (F.comp (leftRepresentable A e)) :=
  eqToIso (congrArg (BalancedTensor.obj A D M) (functorGraph_leftAt A D E F e))

end SerrePositivity.DifferentialGraded
end

end FunctorGraphActions

/-! ## FunctorExtensionEvaluation（旧 SerrePositivity/DifferentialGraded/Module/FunctorExtensionEvaluation.lean） -/

/-! # graph延長と制限の評価成分

## 概要
任意の右E加群の作用をFに沿ってbalanced族へ引き戻す。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section FunctorExtensionEvaluation
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)
  (M : RightModule A E)

omit [Small.{u} D] in
lemma functorGraph_leftAction (e : E) (x y : D) :
    BalancedTensor.leftAction A D ((functorGraph A D E F).leftAt e) x y =
      BalancedTensor.leftAction A D (F.comp (leftRepresentable A e)) x y := by
  change uncurryRight ((F.map x y ≫ yonedaHom A E (F.obj x) (F.obj y)) ≫
    moduleHomπ A E (representable A (F.obj x)) (representable A (F.obj y)) e) =
      uncurryRight (F.map x y ≫ (leftRepresentable A e).map (F.obj x) (F.obj y))
  rw [Category.assoc, yonedaHom_π, endomorphismYonedaApp]

/-- 各D対象でのMの作用を使う全次数balanced族。 -/
def functorExtensionEvaluationFamily (e : E) :
    BalancedTensor.BalancedFamily A D (restrictModule A D E F.op M)
      ((functorGraph A D E F).leftAt e) (M.obj (op e)) := by
  refine ⟨fun d => BalancedTensor.rightAction A E M e (F.obj d), ?_⟩
  intro x y
  have h := (BalancedTensor.restrictFamily A D E F M (leftRepresentable A e)
    (BalancedTensor.leftYonedaFamily A E e M)).property x y
  change (BalancedTensor.rightAction A D (restrictModule A D E F.op M) x y ▷
      homObject A E e (F.obj x)) ≫ BalancedTensor.rightAction A E M e (F.obj x) =
    (α_ (M.obj (op (F.obj y))) (homObject A D x y) (homObject A E e (F.obj x))).hom ≫
      M.obj (op (F.obj y)) ◁ BalancedTensor.leftAction A D
        ((functorGraph A D E F).leftAt e) x y ≫ BalancedTensor.rightAction A E M e (F.obj y)
  rw [functorGraph_leftAction]
  exact h

/-- 延長された制限加群から元の加群への評価chain mapの各対象成分。 -/
def functorExtensionEvaluationComponent (e : E) :
    ((dgModuleExtension A D E F).obj (restrictModule A D E F.op M)).obj (op e) ⟶ M.obj (op e) :=
  BalancedTensor.desc A D _ _ (functorExtensionEvaluationFamily A D E F M e)

@[reassoc] lemma ι_functorExtensionEvaluationComponent (e : E) (d : D) :
    BalancedTensor.ι A D (restrictModule A D E F.op M) ((functorGraph A D E F).leftAt e) d ≫
      functorExtensionEvaluationComponent A D E F M e =
        BalancedTensor.rightAction A E M e (F.obj d) :=
  BalancedTensor.ι_desc A D _ _ _ d

lemma functorExtensionEvaluation_element (e : E) (d : D) {r s n : ℤ}
    (m : (M.obj (op (F.obj d))).X r) (h : GradedHom A e (F.obj d) s) (hn : r + s = n) :
    (functorExtensionEvaluationComponent A D E F M e).f n
      (BalancedTensor.element A D (restrictModule A D E F.op M)
        ((functorGraph A D E F).leftAt e) d m h hn) =
      (r * s).negOnePow • moduleAction A M h m hn := by
  have he := congrArg (fun f => f.f n
    (ιTensorObj (M.obj (op (F.obj d))) (homObject A E e (F.obj d)) r s n hn (m ⊗ₜ[A] h)))
    (ι_functorExtensionEvaluationComponent A D E F M e d)
  exact he.trans (BalancedTensor.rightAction_apply A E M e (F.obj d) r s n hn m h)

end SerrePositivity.DifferentialGraded
end

end FunctorExtensionEvaluation

/-! ## FunctorExtensionCounit（旧 SerrePositivity/DifferentialGraded/Module/FunctorExtensionCounit.lean） -/

/-! # graph tensorの評価と右作用の整合性

## 概要
任意次数の生成元上で二つのKoszul符号を比較し、全Hom自然な閉零射へ束ねる。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section FunctorExtensionCounit
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

lemma dgModuleExtension_action_element (N : RightModule A D) (x y : Eᵒᵖ) (d : D)
    {p r s a j n : ℤ} (ha : r + s = a) (hj : s + p = j) (hn : a + p = n)
    (f : GradedHom A x y p) (m : (N.obj (op d)).X r) (h : GradedHom A x.unop (F.obj d) s) :
    moduleAction A ((dgModuleExtension A D E F).obj N) f
      (BalancedTensor.element A D N ((functorGraph A D E F).leftAt x.unop) d m h ha) hn =
      (p * r).negOnePow • BalancedTensor.element A D N
        ((functorGraph A D E F).leftAt y.unop) d m
        (moduleAction A (representable A (F.obj d)) f h hj) (by omega) :=
  BimoduleTensor.compose_rightAction_element A E D (RightModule A D)
    (functorGraph A D E F) (DGFunctor.id (RightModule A D)) x y d N ha hj hn f m h

variable (M : RightModule A E)

omit [Small.{u} D] [Small.{u} E] in
lemma functorExtensionEvaluation_action (x y : Eᵒᵖ) (d : D) {p r s n : ℤ}
    (f : GradedHom A x y p) (m : (M.obj (op (F.obj d))).X r)
    (h : GradedHom A x.unop (F.obj d) s) (hn : r + s + p = n) :
    (p * r).negOnePow • ((r * (s + p)).negOnePow •
      moduleAction A M (moduleAction A (representable A (F.obj d)) f h rfl) m (by omega)) =
      moduleAction A M f ((r * s).negOnePow • moduleAction A M h m rfl) hn := by
  have hc := moduleAction_representable A (F.obj d) M x y p s r (s + p) n (r + s)
    rfl rfl (by omega) f h m
  rw [hc, moduleAction_units_smul]
  simp only [smul_smul]
  congr 1
  rw [← Int.negOnePow_add]
  have hi : p * r + r * (s + p) = r * s + 2 * (p * r) := by ring
  rw [hi, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]

lemma functorExtensionEvaluation_naturality (x y : Eᵒᵖ) :
    ((dgModuleExtension A D E F).obj (restrictModule A D E F.op M)).map x y ≫
        homPostcompose _ (functorExtensionEvaluationComponent A D E F M y.unop) =
      M.map x y ≫ homPrecompose (functorExtensionEvaluationComponent A D E F M x.unop) _ := by
  apply BalancedTensor.homMap_post_pre_eq A D (restrictModule A D E F.op M)
    ((functorGraph A D E F).leftAt x.unop)
  intro p f d r s a n ha hn m h
  subst a
  change (functorExtensionEvaluationComponent A D E F M y.unop).f n
    (moduleAction A ((dgModuleExtension A D E F).obj (restrictModule A D E F.op M)) f
      (BalancedTensor.element A D (restrictModule A D E F.op M)
        ((functorGraph A D E F).leftAt x.unop) d m h rfl) hn) = _
  rw [dgModuleExtension_action_element A D E F _ x y d rfl rfl hn]
  simp only [Units.smul_def, map_zsmul]
  change (p * r).negOnePow • (functorExtensionEvaluationComponent A D E F M y.unop).f n
    (BalancedTensor.element A D (restrictModule A D E F.op M)
      ((functorGraph A D E F).leftAt y.unop) d m
        (moduleAction A (representable A (F.obj d)) f h rfl) (by omega)) =
    moduleAction A M f ((functorExtensionEvaluationComponent A D E F M x.unop).f (r + s)
      (BalancedTensor.element A D (restrictModule A D E F.op M)
        ((functorGraph A D E F).leftAt x.unop) d m h rfl)) hn
  rw [functorExtensionEvaluation_element, functorExtensionEvaluation_element]
  exact functorExtensionEvaluation_action A D E F M x y d f m h hn

/-- 延長された制限加群から元の加群への実際の全Hom自然な閉零射。 -/
def functorExtensionCounit :
    ForgetEnrichment.of (Complex A)
      ((dgModuleExtension A D E F).obj (restrictModule A D E F.op M)) ⟶
        ForgetEnrichment.of (Complex A) M :=
  moduleMorphismMk A E (fun e => functorExtensionEvaluationComponent A D E F M e.unop)
    (functorExtensionEvaluation_naturality A D E F M)

lemma functorExtensionCounit_eval (e : E) :
    (moduleEvaluation A E e).map (functorExtensionCounit A D E F M) =
      functorExtensionEvaluationComponent A D E F M e := moduleMorphismMk_eval A E _ _ e

end SerrePositivity.DifferentialGraded
end

end FunctorExtensionCounit

/-! ## FunctorExtensionCounitNaturality（旧 SerrePositivity/DifferentialGraded/Module/FunctorExtensionCounitNaturality.lean） -/

/-! # graph延長–制限の余単位の加群変数に関する自然性

## 概要
graph延長–制限の余単位の加群変数に関する自然性。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section FunctorExtensionCounitNaturality
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

def dgModuleCounit :
    moduleRestriction A D E F.op ⋙ (dgModuleExtension A D E F).onClosed ⟶
      𝟭 (ModuleCategory A E) where
  app M := functorExtensionCounit A D E F (ForgetEnrichment.to (Complex A) M)
  naturality {M N} f := by
    apply moduleMorphism_ext
    intro e
    rw [Functor.map_comp, Functor.map_comp, functorExtensionCounit_eval,
      functorExtensionCounit_eval]
    simp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.id_map]
    rw [dgModuleExtension_map_eval]
    apply Cochain.ofHom_injective
    apply BalancedTensor.cochain_zero_element_ext A D
      (restrictModule A D E F.op (ForgetEnrichment.to (Complex A) M))
      ((functorGraph A D E F).leftAt e)
    intro d r s n hn m h
    simp only [Cochain.ofHom_v]
    change (functorExtensionEvaluationComponent A D E F
      (ForgetEnrichment.to (Complex A) N) e).f n
      ((BalancedTensor.rightTensorMap A D ((functorGraph A D E F).leftAt e)
        ((moduleRestriction A D E F.op).map f)).f n
        (BalancedTensor.element A D (restrictModule A D E F.op
          (ForgetEnrichment.to (Complex A) M)) ((functorGraph A D E F).leftAt e) d m h hn)) =
      ((moduleEvaluation A E e).map f).f n
        ((functorExtensionEvaluationComponent A D E F
          (ForgetEnrichment.to (Complex A) M) e).f n
          (BalancedTensor.element A D (restrictModule A D E F.op
            (ForgetEnrichment.to (Complex A) M)) ((functorGraph A D E F).leftAt e) d m h hn))
    refine (congrArg (fun z => (functorExtensionEvaluationComponent A D E F
      (ForgetEnrichment.to (Complex A) N) e).f n z)
      (BalancedTensor.rightTensorMap_element A D ((functorGraph A D E F).leftAt e)
        ((moduleRestriction A D E F.op).map f) d m h hn)).trans ?_
    rw [moduleRestriction_map_eval]
    change (functorExtensionEvaluationComponent A D E F
      (ForgetEnrichment.to (Complex A) N) e).f n
      (BalancedTensor.element A D (restrictModule A D E F.op
        (ForgetEnrichment.to (Complex A) N)) ((functorGraph A D E F).leftAt e) d
        (((moduleEvaluation A E (F.obj d)).map f).f r m) h hn) =
      ((moduleEvaluation A E e).map f).f n
        ((functorExtensionEvaluationComponent A D E F
          (ForgetEnrichment.to (Complex A) M) e).f n
          (BalancedTensor.element A D (restrictModule A D E F.op
            (ForgetEnrichment.to (Complex A) M)) ((functorGraph A D E F).leftAt e) d m h hn))
    rw [functorExtensionEvaluation_element, functorExtensionEvaluation_element]
    simp only [Units.smul_def, map_zsmul]
    have ha := closedFamily_action A
      (fun x : Eᵒᵖ => (moduleEvaluation A E x.unop).map f)
      (fun x y => closedTransApp_naturality A (moduleClosedHomEquiv A E M N f) x y)
      (op (F.obj d)) (op e) s r n hn h m
    exact congrArg (fun z => ((r * s).negOnePow : ℤ) • z) ha.symm

end SerrePositivity.DifferentialGraded
end

end FunctorExtensionCounitNaturality

/-! ## FunctorExtensionInsertion（旧 SerrePositivity/DifferentialGraded/Module/FunctorExtensionInsertion.lean） -/

/-! # graph延長への単位挿入成分と評価による復元

## 概要
graph延長への単位挿入成分と評価による復元。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section FunctorExtensionInsertion
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- N(d)の元とF(d)の閉単位を、対応するtensor生成元へ送る。 -/
def functorExtensionInsertionComponent (N : RightModule A D) (d : D) :
    N.obj (op d) ⟶ ((dgModuleExtension A D E F).obj N).obj (op (F.obj d)) :=
  freeUnitInsert A (F.obj d) (N.obj (op d)) ≫
    BalancedTensor.ι A D N ((functorGraph A D E F).leftAt (F.obj d)) d

lemma functorExtensionInsertion_apply (N : RightModule A D) (d : D) (r : ℤ)
    (m : (N.obj (op d)).X r) :
    (functorExtensionInsertionComponent A D E F N d).f r m =
      BalancedTensor.element A D N ((functorGraph A D E F).leftAt (F.obj d)) d
        m (unitElement A (F.obj d)).val (add_zero r) := by
  change (BalancedTensor.ι A D N ((functorGraph A D E F).leftAt (F.obj d)) d).f r
    ((freeUnitInsert A (F.obj d) (N.obj (op d))).f r m) = _
  rw [freeUnitInsert_apply]
  rfl

/-- 制限加群の値を挿入して評価すると元に戻る。 -/
lemma functorExtensionInsertion_evaluation (M : RightModule A E) (d : D) :
    functorExtensionInsertionComponent A D E F (restrictModule A D E F.op M) d ≫
      functorExtensionEvaluationComponent A D E F M (F.obj d) = 𝟙 (M.obj (op (F.obj d))) := by
  apply chain_ext_apply
  intro r m
  rw [chain_comp_apply, functorExtensionInsertion_apply, functorExtensionEvaluation_element]
  simp only [mul_zero, Int.negOnePow_zero, one_smul]
  exact moduleAction_unit A M (op (F.obj d)) r m

end SerrePositivity.DifferentialGraded
end

end FunctorExtensionInsertion

/-! ## FunctorExtensionUnit（旧 SerrePositivity/DifferentialGraded/Module/FunctorExtensionUnit.lean） -/

/-! # graph延長–制限の全Hom自然な単位射

## 概要
graph延長–制限の全Hom自然な単位射。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section FunctorExtensionUnit
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

omit [Small.{u} D] in
lemma functorGraph_leftAction_unit (x y : D) {p : ℤ} (f : GradedHom A x y p) :
    leftAction A ((functorGraph A D E F).leftAt (F.obj x)) f
      (unitElement A (F.obj x)).val (zero_add p) = (F.map x y).f p f := by
  change (((F.map x y ≫ yonedaHom A E (F.obj x) (F.obj y)) ≫
    moduleHomπ A E (representable A (F.obj x)) (representable A (F.obj y))
      (F.obj x)).f p f).v 0 p (zero_add p) (unitElement A (F.obj x)).val = _
  rw [Category.assoc, yonedaHom_π, endomorphismYonedaApp]
  change leftAction A (leftRepresentable A (F.obj x)) ((F.map x y).f p f)
    (unitElement A (F.obj x)).val (zero_add p) = _
  rw [leftRepresentable_action, mul_zero, Int.negOnePow_zero, one_smul, forward_unit]

lemma functorExtensionInsertion_action (N : RightModule A D) (x y : Dᵒᵖ)
    {p r n : ℤ} (f : GradedHom A x y p) (m : (N.obj x).X r) (hn : r + p = n) :
    (functorExtensionInsertionComponent A D E F N y.unop).f n
      (moduleAction A N f m hn) =
    moduleAction A (restrictModule A D E F.op ((dgModuleExtension A D E F).obj N)) f
      ((functorExtensionInsertionComponent A D E F N x.unop).f r m) hn := by
  subst n
  have hn : r + p = r + p := rfl
  rw [functorExtensionInsertion_apply, functorExtensionInsertion_apply, restrictModule_action]
  rw [dgModuleExtension_action_element A D E F N (op (F.obj x.unop))
    (op (F.obj y.unop)) x.unop (add_zero r) (zero_add p) hn]
  rw [representable_action, unit_forward]
  have hb := BalancedTensor.element_balanced_zero A D N
    ((functorGraph A D E F).leftAt (F.obj y.unop)) y.unop x.unop m f
      (unitElement A (F.obj y.unop)).val
  have hu := functorGraph_leftAction_unit A D E F y.unop x.unop f
  change leftAction A ((functorGraph A D E F).leftAt (F.obj y.unop)) f
    (unitElement A (F.obj y.unop)).val (by omega) = (F.map y.unop x.unop).f p f at hu
  have hbb : (r * p).negOnePow • BalancedTensor.element A D N
      ((functorGraph A D E F).leftAt (F.obj y.unop)) y.unop
        (moduleAction A N f m hn) (unitElement A (F.obj y.unop)).val (add_zero (r + p)) =
    BalancedTensor.element A D N ((functorGraph A D E F).leftAt (F.obj y.unop)) x.unop m
      ((F.map y.unop x.unop).f p f) hn := by
    exact hb.trans (congrArg (fun z => BalancedTensor.element A D N
      ((functorGraph A D E F).leftAt (F.obj y.unop)) x.unop m z
        (by omega : r + p = r + p)) hu)
  have hc := congrArg (fun z => (r * p).negOnePow • z) hbb
  rw [smul_smul, Int.units_mul_self, one_smul] at hc
  change BalancedTensor.element A D N ((functorGraph A D E F).leftAt (F.obj y.unop))
    y.unop (moduleAction A N f m rfl) (unitElement A (F.obj y.unop)).val (add_zero (r + p)) =
    (p * r).negOnePow • BalancedTensor.element A D N
      ((functorGraph A D E F).leftAt (F.obj y.unop)) x.unop m
        ((F.map y.unop x.unop).f p f) rfl
  rw [mul_comm r p] at hc
  exact hc

/-- 各対象への単位挿入を全Hom自然な閉零加群射に束ねる。 -/
def functorExtensionUnit (N : RightModule A D) :
    ForgetEnrichment.of (Complex A) N ⟶ ForgetEnrichment.of (Complex A)
      (restrictModule A D E F.op ((dgModuleExtension A D E F).obj N)) :=
  moduleMorphismMk A D (fun x => functorExtensionInsertionComponent A D E F N x.unop)
    (closedFamily_of_action A _ (fun x y _ _ _ hn f m =>
      functorExtensionInsertion_action A D E F N x y f m hn))

lemma functorExtensionUnit_eval (N : RightModule A D) (d : D) :
    (moduleEvaluation A D d).map (functorExtensionUnit A D E F N) =
      functorExtensionInsertionComponent A D E F N d := moduleMorphismMk_eval A D _ _ d

end SerrePositivity.DifferentialGraded
end

end FunctorExtensionUnit

/-! ## FunctorExtensionUnitNaturality（旧 SerrePositivity/DifferentialGraded/Module/FunctorExtensionUnitNaturality.lean） -/

/-! # graph延長–制限の単位の加群変数に関する自然性

## 概要
graph延長–制限の単位の加群変数に関する自然性。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section FunctorExtensionUnitNaturality
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

lemma functorExtensionInsertion_map {M N : ModuleCategory A D} (f : M ⟶ N) (d : D) :
    (moduleEvaluation A D d).map f ≫ functorExtensionInsertionComponent A D E F
        (ForgetEnrichment.to (Complex A) N) d =
      functorExtensionInsertionComponent A D E F (ForgetEnrichment.to (Complex A) M) d ≫
        (moduleEvaluation A E (F.obj d)).map ((dgModuleExtension A D E F).onClosed.map f) := by
  rw [dgModuleExtension_map_eval]
  apply chain_ext_apply
  intro r m
  change (functorExtensionInsertionComponent A D E F
    (ForgetEnrichment.to (Complex A) N) d).f r
      (((moduleEvaluation A D d).map f).f r m) =
    (BalancedTensor.rightTensorMap A D ((functorGraph A D E F).leftAt (F.obj d)) f).f r
      ((functorExtensionInsertionComponent A D E F
        (ForgetEnrichment.to (Complex A) M) d).f r m)
  rw [functorExtensionInsertion_apply, functorExtensionInsertion_apply]
  exact (BalancedTensor.rightTensorMap_element A D
    ((functorGraph A D E F).leftAt (F.obj d)) f d m
      (unitElement A (F.obj d)).val (add_zero r)).symm

/-- 通常dg加群圏の延長–制限に対する自然な単位。 -/
def dgModuleUnit : 𝟭 (ModuleCategory A D) ⟶
    (dgModuleExtension A D E F).onClosed ⋙ moduleRestriction A D E F.op where
  app M := functorExtensionUnit A D E F (ForgetEnrichment.to (Complex A) M)
  naturality {M N} f := by
    apply moduleMorphism_ext
    intro d
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      functorExtensionUnit_eval, functorExtensionUnit_eval]
    simp only [CategoryTheory.Functor.id_map, CategoryTheory.Functor.comp_map]
    rw [moduleRestriction_map_eval]
    exact functorExtensionInsertion_map A D E F f d

end SerrePositivity.DifferentialGraded
end

end FunctorExtensionUnitNaturality

/-! ## FunctorExtensionAdjunction（旧 SerrePositivity/DifferentialGraded/Module/FunctorExtensionAdjunction.lean） -/

/-! # graph tensor延長とdg関手に沿う制限の随伴

## 概要
graph tensor延長とdg関手に沿う制限の随伴。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section FunctorExtensionAdjunction
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

lemma dgModule_right_triangle (M : ModuleCategory A E) :
    (dgModuleUnit A D E F).app ((moduleRestriction A D E F.op).obj M) ≫
      (moduleRestriction A D E F.op).map ((dgModuleCounit A D E F).app M) = 𝟙 _ := by
  apply moduleMorphism_ext
  intro d
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
  change (moduleEvaluation A D d).map (functorExtensionUnit A D E F
      (restrictModule A D E F.op (ForgetEnrichment.to (Complex A) M))) ≫
    (moduleEvaluation A D d).map ((moduleRestriction A D E F.op).map
      (functorExtensionCounit A D E F (ForgetEnrichment.to (Complex A) M))) = _
  rw [functorExtensionUnit_eval, moduleRestriction_map_eval, functorExtensionCounit_eval]
  exact functorExtensionInsertion_evaluation A D E F (ForgetEnrichment.to (Complex A) M) d

lemma dgModule_left_triangle (M : ModuleCategory A D) :
    (dgModuleExtension A D E F).onClosed.map ((dgModuleUnit A D E F).app M) ≫
      (dgModuleCounit A D E F).app ((dgModuleExtension A D E F).onClosed.obj M) = 𝟙 _ := by
  apply moduleMorphism_ext
  intro e
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
  change (moduleEvaluation A E e).map ((dgModuleExtension A D E F).onClosed.map
      (functorExtensionUnit A D E F (ForgetEnrichment.to (Complex A) M))) ≫
    (moduleEvaluation A E e).map (functorExtensionCounit A D E F
      ((dgModuleExtension A D E F).obj (ForgetEnrichment.to (Complex A) M))) = _
  rw [dgModuleExtension_map_eval, functorExtensionCounit_eval]
  apply Cochain.ofHom_injective
  apply BalancedTensor.cochain_zero_element_ext A D
    (ForgetEnrichment.to (Complex A) M) ((functorGraph A D E F).leftAt e)
  intro d r s n hn m h
  simp only [Cochain.ofHom_v]
  change (functorExtensionEvaluationComponent A D E F
      ((dgModuleExtension A D E F).obj (ForgetEnrichment.to (Complex A) M)) e).f n
    ((BalancedTensor.rightTensorMap A D ((functorGraph A D E F).leftAt e)
      (functorExtensionUnit A D E F (ForgetEnrichment.to (Complex A) M))).f n
      (BalancedTensor.element A D (ForgetEnrichment.to (Complex A) M)
        ((functorGraph A D E F).leftAt e) d m h hn)) =
    BalancedTensor.element A D (ForgetEnrichment.to (Complex A) M)
      ((functorGraph A D E F).leftAt e) d m h hn
  refine (congrArg (fun z => (functorExtensionEvaluationComponent A D E F
    ((dgModuleExtension A D E F).obj (ForgetEnrichment.to (Complex A) M)) e).f n z)
    (BalancedTensor.rightTensorMap_element A D ((functorGraph A D E F).leftAt e)
      (functorExtensionUnit A D E F (ForgetEnrichment.to (Complex A) M)) d m h hn)).trans ?_
  rw [functorExtensionUnit_eval]
  change (functorExtensionEvaluationComponent A D E F
      ((dgModuleExtension A D E F).obj (ForgetEnrichment.to (Complex A) M)) e).f n
    (BalancedTensor.element A D
      (restrictModule A D E F.op
        ((dgModuleExtension A D E F).obj (ForgetEnrichment.to (Complex A) M)))
      ((functorGraph A D E F).leftAt e) d
      ((functorExtensionInsertionComponent A D E F
        (ForgetEnrichment.to (Complex A) M) d).f r m) h hn) = _
  rw [functorExtensionInsertion_apply]
  rw [functorExtensionEvaluation_element,
    dgModuleExtension_action_element A D E F _ (op (F.obj d)) (op e) d
      (add_zero r) (zero_add s) hn, representable_action, unit_forward]
  simp only [smul_smul, mul_comm s r, Int.units_mul_self, one_smul]

/-- 任意のdg関手について、全dg加群の閉零射圏上でgraph延長は制限の左随伴。 -/
def dgModuleExtensionRestrictionAdjunction :
    (dgModuleExtension A D E F).onClosed ⊣ moduleRestriction A D E F.op :=
  Adjunction.mkOfUnitCounit {
    unit := dgModuleUnit A D E F
    counit := dgModuleCounit A D E F
    left_triangle := by
      apply NatTrans.ext
      funext M
      simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.associator_hom_app, Category.id_comp, Category.comp_id,
        Functor.comp_obj, Functor.id_obj, NatTrans.id] using dgModule_left_triangle A D E F M
    right_triangle := by
      apply NatTrans.ext
      funext M
      simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.associator_inv_app, Category.id_comp, Category.comp_id,
        Functor.comp_obj, Functor.id_obj, NatTrans.id] using dgModule_right_triangle A D E F M }

end SerrePositivity.DifferentialGraded
end

end FunctorExtensionAdjunction

/-! ## FunctorExtensionRepresentableUnit（旧 SerrePositivity/DifferentialGraded/Module/FunctorExtensionRepresentableUnit.lean） -/

/-! # 代表加群上での延長–制限単位とdg関手のHom比較の一致

## 概要
代表加群上での延長–制限単位とdg関手のHom比較の一致。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section FunctorExtensionRepresentableUnit
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

lemma functorExtensionUnit_representable (d : D) :
    functorExtensionUnit A D E F (representable A d) ≫
      (moduleRestriction A D E F.op).map (dgModuleExtensionRepresentableIso A D E F d).hom =
        representableRestrictionMap A D E F d := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, functorExtensionUnit_eval,
    moduleRestriction_map_eval, representableRestrictionMap_eval]
  change functorExtensionInsertionComponent A D E F (representable A d) x ≫
    (moduleEvaluation A E (F.obj x)).map
      (BimoduleTensor.rightUnitIso A E D (functorGraph A D E F) d).hom = F.map x d
  rw [BimoduleTensor.rightUnitIso_hom_eval]
  change functorExtensionInsertionComponent A D E F (representable A d) x ≫
    BalancedTensor.yonedaEvaluation A D d ((functorGraph A D E F).leftAt (F.obj x)) = _
  apply chain_ext_apply
  intro r f
  change (BalancedTensor.yonedaEvaluation A D d
    ((functorGraph A D E F).leftAt (F.obj x))).f r
      ((functorExtensionInsertionComponent A D E F (representable A d) x).f r f) =
    (F.map x d).f r f
  rw [functorExtensionInsertion_apply, BalancedTensor.yonedaEvaluation_element]
  exact functorGraph_leftAction_unit A D E F x d f

lemma functorExtensionUnit_representable_quasiIso (hF : HomQuasiIso F) (d : D) :
    moduleQuasiIso A D (functorExtensionUnit A D E F (representable A d)) := by
  have hg : moduleQuasiIso A D ((moduleRestriction A D E F.op).map
      (dgModuleExtensionRepresentableIso A D E F d).hom) := fun x => by infer_instance
  have hfg : moduleQuasiIso A D (functorExtensionUnit A D E F (representable A d) ≫
      (moduleRestriction A D E F.op).map (dgModuleExtensionRepresentableIso A D E F d).hom) := by
    rw [functorExtensionUnit_representable]
    exact representableRestrictionMap_quasiIso A D E F hF d
  exact (moduleQuasiIso A D).of_postcomp _ _ hg hfg

end SerrePositivity.DifferentialGraded
end

end FunctorExtensionRepresentableUnit

/-! ## ExtensionFreeAdjunction（旧 SerrePositivity/DifferentialGraded/Module/ExtensionFreeAdjunction.lean） -/

/-!
概要：実 dg 加群延長と任意複体で生成する自由加群の比較を、随伴の一意性で構成する。
方針：自由・評価随伴と延長・制限随伴を合成し、制限後の評価を同じ標的評価へ戻す。
規約：生成複体の全射に自然な実同型を構成し、元の shift 比較は変更しない。
使われ方：c′ のシフト自由閉射と実延長の端点比較。
-/

@[expose] public section ExtensionFreeAdjunction
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
private lemma extensionFreeComparison_homEquiv
    {C₀ C₁ : Type*} [Category C₀] [Category C₁]
    {L L' : C₀ ⥤ C₁} {H : C₁ ⥤ C₀} (adj : L ⊣ H) (adj' : L' ⊣ H)
    (x : C₀) (M : C₁) (g : L'.obj x ⟶ M) :
    adj.homEquiv x M ((Adjunction.leftAdjointUniq adj adj').hom.app x ≫ g) =
      adj'.homEquiv x M g := by
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app]
  exact (adj'.homEquiv_unit x M g).symm

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R D E)

def dgModuleExtensionFreeAdjunction (x : D) :
    freeAt (A := R) x ⋙ (dgModuleExtension R D E F).onClosed ⊣
      moduleEvaluation R E (F.obj x) :=
  (((freeEvaluationAdjunction R D x).comp (dgModuleExtensionRestrictionAdjunction R D E F)).ofNatIsoRight
    (moduleRestrictionEvaluationIso R D E F.op x))

def dgModuleExtensionFreeFunctorIso (x : D) :
    freeAt (A := R) x ⋙ (dgModuleExtension R D E F).onClosed ≅ freeAt (A := R) (F.obj x) :=
  Adjunction.leftAdjointUniq (dgModuleExtensionFreeAdjunction R D E F x)
    (freeEvaluationAdjunction R E (F.obj x))

lemma dgModuleExtensionFreeAdjunction_homEquiv (x : D) (K : Complex R)
    (M : ModuleCategory R E)
    (g : (dgModuleExtension R D E F).onClosed.obj ((freeAt x).obj K) ⟶ M) :
    (dgModuleExtensionFreeAdjunction R D E F x).homEquiv K M g =
    freeHomEquiv R D x K ((moduleRestriction R D E F.op).obj M)
      ((dgModuleExtensionRestrictionAdjunction R D E F).homEquiv ((freeAt x).obj K) M g) := by
  rw [dgModuleExtensionFreeAdjunction, Adjunction.homEquiv_ofNatIsoRight_apply]
  rw [Adjunction.comp_homEquiv]
  simp only [freeEvaluationAdjunction, Adjunction.mkOfHomEquiv_homEquiv,
    moduleRestrictionEvaluationIso, NatIso.ofComponents_hom_app, Iso.refl_hom, Category.comp_id]
  rfl

def dgModuleExtensionFreeAtIso (x : D) (K : Complex R) :
    (dgModuleExtension R D E F).onClosed.obj ((freeAt x).obj K) ≅ (freeAt (F.obj x)).obj K :=
  (dgModuleExtensionFreeFunctorIso R D E F x).app K

lemma dgModuleExtensionFreeAtIso_naturality (x : D) {K L : Complex R} (g : K ⟶ L) :
    (dgModuleExtension R D E F).onClosed.map ((freeAt x).map g) ≫
      (dgModuleExtensionFreeAtIso R D E F x L).hom =
    (dgModuleExtensionFreeAtIso R D E F x K).hom ≫ (freeAt (F.obj x)).map g :=
  (dgModuleExtensionFreeFunctorIso R D E F x).hom.naturality g

set_option maxRecDepth 1024 in
lemma dgModuleExtensionFreeAtIso_homEquiv (x : D) (K : Complex R)
    (M : ModuleCategory R E) (g : (freeAt (F.obj x)).obj K ⟶ M) :
    (dgModuleExtensionFreeAdjunction R D E F x).homEquiv K M
      ((dgModuleExtensionFreeAtIso R D E F x K).hom ≫ g) =
    (freeEvaluationAdjunction R E (F.obj x)).homEquiv K M g :=
  extensionFreeComparison_homEquiv (dgModuleExtensionFreeAdjunction R D E F x)
    (freeEvaluationAdjunction R E (F.obj x)) K M g

end SerrePositivity.DifferentialGraded
end

end ExtensionFreeAdjunction

/-! ## ExtensionFreeUnitComparison（旧 SerrePositivity/DifferentialGraded/Module/ExtensionFreeUnitComparison.lean） -/

/-!
概要：実自由延長同型の随伴射を、元の Hom 鎖写像による制限比較へ同定する。
方針：自由評価の Hom 同値で両射を比較し、随伴一意性の特徴式を用いる。
規約：元の実延長同型と、各成分が恒等 tensor Hom 写像である閉射を保持する。
使われ方：c′ の全シフト自由閉射の端点同型付き延長比較。
-/

@[expose] public section ExtensionFreeUnitComparison
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R D E)

set_option maxRecDepth 1024 in
lemma dgModuleExtensionFreeAtIso_adjunct (x : D) (K : Complex R) :
    (dgModuleExtensionRestrictionAdjunction R D E F).homEquiv ((freeAt x).obj K)
      ((freeAt (F.obj x)).obj K) (dgModuleExtensionFreeAtIso R D E F x K).hom =
    freeRestrictionComparison R D E F x K := by
  apply (freeHomEquiv R D x K
    ((moduleRestriction R D E F.op).obj ((freeAt (F.obj x)).obj K))).injective
  have h := dgModuleExtensionFreeAtIso_homEquiv R D E F x K
    ((freeAt (F.obj x)).obj K) (𝟙 _)
  simp only [Category.comp_id] at h
  rw [dgModuleExtensionFreeAdjunction_homEquiv] at h
  have h' := freeRestrictionComparison_freeHomEquiv R D E F x K
  apply h.trans
  simpa only [freeEvaluationAdjunction, Adjunction.mkOfHomEquiv_homEquiv] using h'.symm

end SerrePositivity.DifferentialGraded
end

end ExtensionFreeUnitComparison

/-! ## ExtensionFreeNaturality（旧 SerrePositivity/DifferentialGraded/Module/ExtensionFreeNaturality.lean） -/

/-!
概要：任意の二つの自由加群間の閉射について、実延長と元の Hom 係数への作用を比較する。
方針：延長制限随伴と自由評価同値で射を検出し、自由制限比較の成分を用いる。
規約：同じ実延長関手・実端点同型を保ち、生成複体の次数を制限しない。
使われ方：c′ の全シフト自由閉射を端点輸送込みで共通提示へ戻す。
-/

@[expose] public section ExtensionFreeNaturality
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R D E)

def dgFreeClosedArrowImage (x y : D) (K L : Complex R)
    (g : (freeAt x).obj K ⟶ (freeAt y).obj L) :
    (freeAt (F.obj x)).obj K ⟶ (freeAt (F.obj y)).obj L :=
  (freeHomEquiv R E (F.obj x) K ((freeAt (F.obj y)).obj L)).symm
    (freeHomEquiv R D x K ((freeAt y).obj L) g ≫ (𝟙 L ⊗ₘ F.map x y))

set_option maxRecDepth 1024 in
lemma dgModuleExtensionFreeAtIso_arrow_comm (x y : D) (K L : Complex R)
    (g : (freeAt x).obj K ⟶ (freeAt y).obj L) :
    (dgModuleExtension R D E F).onClosed.map g ≫ (dgModuleExtensionFreeAtIso R D E F y L).hom =
    (dgModuleExtensionFreeAtIso R D E F x K).hom ≫ dgFreeClosedArrowImage R D E F x y K L g := by
  apply ((dgModuleExtensionRestrictionAdjunction R D E F).homEquiv ((freeAt x).obj K)
    ((freeAt (F.obj y)).obj L)).injective
  apply (freeHomEquiv R D x K
    ((moduleRestriction R D E F.op).obj ((freeAt (F.obj y)).obj L))).injective
  rw [Adjunction.homEquiv_naturality_left, dgModuleExtensionFreeAtIso_adjunct,
    freeHomEquiv_naturality_right, freeRestrictionComparison_eval]
  rw [← dgModuleExtensionFreeAdjunction_homEquiv, dgModuleExtensionFreeAtIso_homEquiv]
  simp only [freeEvaluationAdjunction, Adjunction.mkOfHomEquiv_homEquiv,
    dgFreeClosedArrowImage, Equiv.apply_symm_apply]

end SerrePositivity.DifferentialGraded
end

end ExtensionFreeNaturality

/-! ## FreeSphereImageCoefficient（旧 SerrePositivity/DifferentialGraded/Module/FreeSphereImageCoefficient.lean） -/

/-!
概要：自由 sphere 閉射への実 dg 関手作用の係数は、元の Hom 鎖写像の作用と一致する。
方針：自由評価の自然性と sphere tensor shift 比較の自然性を同じ cycle に適用する。
規約：全整数次数と元の実閉射を保つ。
使われ方：c′ のコード内閉射と、実延長で写した元の閉射の照合。
-/

@[expose] public section FreeSphereImageCoefficient
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R D E)

lemma dgFreeClosedArrowImage_sphere_coefficient (x y : D) (n m : ℤ)
    (g : freeSphere R D x n ⟶ freeSphere R D y m) :
    freeSphereClosedCoefficient R E (F.obj x) (F.obj y) n m
      (dgFreeClosedArrowImage R D E F x y (complexSphere R n) (complexSphere R m) g) =
      (F.map x y).f (n - m) (freeSphereClosedCoefficient R D x y n m g) := by
  have hz : (freeSphereHomEquiv R E (F.obj x) n (freeSphere R E (F.obj y) m)
      (dgFreeClosedArrowImage R D E F x y (complexSphere R n) (complexSphere R m) g)).val =
      (𝟙 (complexSphere R m) ⊗ₘ F.map x y).f n
        (freeSphereHomEquiv R D x n (freeSphere R D y m) g).val := by
    change (complexSphereHomEquiv R _ n
      (freeHomEquiv R E (F.obj x) (complexSphere R n) (freeSphere R E (F.obj y) m)
        (dgFreeClosedArrowImage R D E F x y (complexSphere R n) (complexSphere R m) g))).val = _
    rw [dgFreeClosedArrowImage, Equiv.apply_symm_apply]
    exact complexSphereHomEquiv_naturality_val R n _ _
  change (complexSphereTensorShiftIso R m (homObject R E (F.obj x) (F.obj y))).hom.f n _ = _
  rw [hz]
  exact congrArg (fun φ => φ.f n (freeSphereHomEquiv R D x n (freeSphere R D y m) g).val)
    (complexSphereTensorShiftIso_naturality R m (F.map x y))

end SerrePositivity.DifferentialGraded
end

end FreeSphereImageCoefficient

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "4.6.2.17" (partial := special) "仮定：通常の可換環の準同型、または小さい dg 圏の dg 関手（Lean が強い：通常圏と通常の導来圏に限る）。結論：加群の制限に対してテンソルによる拡大が左随伴となり、dg では導来拡大・制限にも随伴を構成する（この仮定での HA の結論の一部に一致）。一般の左テンソル ∞ 圏は含まれない。"] _root_.SerrePositivity.DifferentialGraded.dgModuleExtensionRestrictionAdjunction
