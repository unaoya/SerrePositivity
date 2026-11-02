module

public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations
public import SerrePositivity.DifferentialGraded.Module.Basic
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison
public import SerrePositivity.DifferentialGraded.Complexes.Cone
public import SerrePositivity.DifferentialGraded.Module.Graded

/-!
# Module.ConeConstruction

## 概要
13 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## ShiftHom（旧 SerrePositivity/DifferentialGraded/Module/ShiftHom.lean） -/

/-! # 整数 shift の全次数加群 Hom chain map -/

@[expose] public section ShiftHom
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全次数自然変換を shift の dg 関手で後合成する。パラメータは動かさない。 -/
def shiftModuleParamTrans (s : ℤ) {K : Complex A} {M N : RightModule A D}
    (τ : ModuleParamTrans A D K M N) :
    ModuleParamTrans A D K (shiftModule s M) (shiftModule s N) where
  app x := τ.app x ≫ shiftHom s (M.obj x) (N.obj x)
  naturality x y := by
    let a : ∀ z : Dᵒᵖ, K ⟶ homComplex A (M.obj z) (N.obj z) := fun z => τ.app z
    have ha : (β_ K (x ⟶[Complex A] y)).hom ≫
        (M.map x y ⊗ₘ a y) ≫ enrichedComposition _ _ _ =
        (a x ⊗ₘ N.map x y) ≫ enrichedComposition _ _ _ := τ.naturality x y
    change (β_ K (x ⟶[Complex A] y)).hom ≫
      ((M.map x y ≫ shiftHom s _ _) ⊗ₘ (a y ≫ shiftHom s _ _)) ≫
        enrichedComposition _ _ _ =
      ((a x ≫ shiftHom s _ _) ⊗ₘ (N.map x y ≫ shiftHom s _ _)) ≫
        enrichedComposition _ _ _
    rw [← tensorHom_comp_tensorHom_assoc, ← tensorHom_comp_tensorHom_assoc,
      ← shiftHom_comp, ← shiftHom_comp]
    simpa only [Category.assoc] using congrArg (fun f => f ≫ shiftHom s (M.obj x) (N.obj y)) ha

/-- Hom end の整数 shift。成分は次数 p で (-1)^(sp) を掛ける chain map。 -/
def moduleShiftHom (s : ℤ) (M N : RightModule A D) :
    moduleHom A D M N ⟶ moduleHom A D (shiftModule s M) (shiftModule s N) :=
  (moduleHomEquiv A D _ _ _).symm
    (shiftModuleParamTrans A D s (moduleHomEquiv A D _ M N (𝟙 _)))

@[reassoc]
lemma moduleShiftHom_π (s : ℤ) (M N : RightModule A D) (x : D) :
    moduleShiftHom A D s M N ≫ moduleHomπ A D (shiftModule s M) (shiftModule s N) x =
      moduleHomπ A D M N x ≫ shiftHom s (M.obj (op x)) (N.obj (op x)) := by
  rw [moduleShiftHom, moduleHomEquiv_symm_π]
  change (𝟙 _ ≫ moduleHomπ A D M N x) ≫ shiftHom s _ _ = _
  rw [Category.id_comp]

/-- 全次数 end の shift の成分。特に次数 −1 でも Koszul 符号を保持する。 -/
lemma moduleShiftHom_π_v (s : ℤ) (M N : RightModule A D) (x : D)
    (p i j : ℤ) (hij : i + p = j) (h : (moduleHom A D M N).X p) :
    ((moduleHomπ A D (shiftModule s M) (shiftModule s N) x).f p
      ((moduleShiftHom A D s M N).f p h)).v i j hij =
      (s * p).negOnePow • ((moduleHomπ A D M N x).f p h).v
        (i + s) (j + s) (by omega) := by
  have he := congrArg (fun f => f.f p h) (moduleShiftHom_π A D s M N x)
  change (moduleHomπ A D (shiftModule s M) (shiftModule s N) x).f p
      ((moduleShiftHom A D s M N).f p h) =
    (shiftHom s (M.obj (op x)) (N.obj (op x))).f p ((moduleHomπ A D M N x).f p h) at he
  rw [he, shiftHom_v]

lemma moduleShiftHom_identity (s : ℤ) (M : RightModule A D) :
    moduleIdentity A D M ≫ moduleShiftHom A D s M M =
      moduleIdentity A D (shiftModule s M) := by
  apply moduleHom_ext
  intro x
  rw [Category.assoc, moduleShiftHom_π, moduleIdentity_π,
    ← Category.assoc, moduleIdentity_π, shiftHom_identity]

lemma moduleShiftHom_comp (s : ℤ) (M N P : RightModule A D) :
    moduleComposition A D M N P ≫ moduleShiftHom A D s M P =
      (moduleShiftHom A D s M N ⊗ₘ moduleShiftHom A D s N P) ≫
        moduleComposition A D (shiftModule s M) (shiftModule s N) (shiftModule s P) := by
  apply moduleHom_ext
  intro x
  simp only [Category.assoc, moduleShiftHom_π, moduleComposition_π,
    moduleComposition_π_assoc]
  rw [shiftHom_comp]
  rw [tensorHom_comp_tensorHom_assoc (moduleShiftHom A D s M N)
    (moduleShiftHom A D s N P), moduleShiftHom_π, moduleShiftHom_π,
    tensorHom_comp_tensorHom_assoc]

/-- 整数 shift は加群圏の主モデルでも真の dg 関手。 -/
def moduleShiftDG (s : ℤ) : DGFunctor A (RightModule A D) (RightModule A D) where
  obj := shiftModule s
  map := moduleShiftHom A D s
  map_id := moduleShiftHom_identity A D s
  map_comp := moduleShiftHom_comp A D s

/-- 複体の閉零射の shift は全次数 Hom shift の次数零制限。 -/
lemma shiftHom_closedMap (s : ℤ) {P Q : Complex A} (f : P ⟶ Q) :
    closedMap A f ≫ shiftHom s P Q = closedMap A (f⟦s⟧') := by
  apply (unitCycleEquiv _).injective
  apply Subtype.ext
  change (cycleFromUnit _ (closedMap A f ≫ shiftHom s P Q)).val =
    (cycleFromUnit _ (closedMap A (f⟦s⟧'))).val
  rw [cycleFromUnit_postcomp, closedMap_cycle, shiftHom_ofHom, closedMap_cycle]

/-- 主 dg shift の閉零射の評価は、既存の複体 shift。 -/
lemma moduleShiftDG_map_eval (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).map ((moduleShiftDG A D s).onClosed.map f) =
      ((moduleEvaluation A D x).map f)⟦s⟧' := by
  apply (complexClosedHomEquiv A _ _).symm.injective
  change closedMap A ((moduleEvaluation A D x).map ((moduleShiftDG A D s).onClosed.map f)) =
    closedMap A (((moduleEvaluation A D x).map f)⟦s⟧')
  rw [moduleEvaluation_closedMap]
  change (ForgetEnrichment.homTo (Complex A) (C := RightModule A D) (X := M) (Y := N) f ≫
    moduleShiftHom A D s (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N)) ≫
    moduleHomπ A D (shiftModule s (ForgetEnrichment.to (Complex A) M))
      (shiftModule s (ForgetEnrichment.to (Complex A) N)) x = _
  rw [Category.assoc, moduleShiftHom_π, ← Category.assoc,
    ← moduleEvaluation_closedMap, shiftHom_closedMap]
  rfl

/-- 全次数 dg shift の閉零制限と U7 の具体的 shift は同じ射を持つ。 -/
lemma moduleShiftDG_map_eq (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleShiftDG A D s).onClosed.map f = moduleShiftMap A D s f := by
  apply moduleMorphism_ext
  intro x
  rw [moduleShiftDG_map_eval, moduleShiftMap_eval]

lemma moduleShiftDG_onClosed_eq (s : ℤ) :
    (moduleShiftDG A D s).onClosed = moduleShiftFunctor A D s := by
  apply CategoryTheory.Functor.ext
  swap
  · intro M
    rfl
  · intro M N f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change (moduleShiftDG A D s).onClosed.map f = moduleShiftMap A D s f
    exact moduleShiftDG_map_eq A D s f

end SerrePositivity.DifferentialGraded
end

end ShiftHom

/-! ## ShiftElements（旧 SerrePositivity/DifferentialGraded/Module/ShiftElements.lean） -/

/-! # 全Homのshift射を斉次要素へ適用した成分と微分 -/

@[expose] public section ShiftElements
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleShiftHomElement_π (s : ℤ) {M N : RightModule A D} (q : ℤ)
    (z : (moduleHom A D M N).X q) (x : D) :
    (moduleHomπ A D (shiftModule s M) (shiftModule s N) x).f q
      ((moduleShiftHom A D s M N).f q z) =
        (s * q).negOnePow • ((moduleHomπ A D M N x).f q z).shift s := by
  have h := congrArg (fun f => f.f q z) (moduleShiftHom_π A D s M N x)
  change (moduleHomπ A D (shiftModule s M) (shiftModule s N) x).f q
    ((moduleShiftHom A D s M N).f q z) =
      (shiftHom s (M.obj (Opposite.op x)) (N.obj (Opposite.op x))).f q
        ((moduleHomπ A D M N x).f q z) at h
  exact h.trans (shiftHom_apply s _ _ q _)

lemma moduleShiftHomElement_d (s : ℤ) {M N : RightModule A D} (q r : ℤ)
    (z : (moduleHom A D M N).X q) :
    (moduleHom A D (shiftModule s M) (shiftModule s N)).d q r
      ((moduleShiftHom A D s M N).f q z) =
        (moduleShiftHom A D s M N).f r ((moduleHom A D M N).d q r z) :=
  congrArg (fun f => f z) ((moduleShiftHom A D s M N).comm q r)

end SerrePositivity.DifferentialGraded
end

end ShiftElements

/-! ## Restriction（旧 SerrePositivity/DifferentialGraded/Module/Restriction.lean） -/

/-! # dg関手に沿った右加群の制限と全Hom自然な閉零射

## 概要
dg関手に沿った右加群の制限と全Hom自然な閉零射。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Module/RestrictionAction.lean、Module/
RestrictionColimits.lean、Module/RestrictionGradedSplit.lean等。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・
K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section Restriction
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [DGCategory A E]

/-- opposite上のdg関手に前合成する。全次数の作用を保持する。 -/
def restrictModule (F : DGFunctor A Dᵒᵖ Eᵒᵖ) (M : RightModule A E) : RightModule A D :=
  F.comp M.toFunctor

variable [Small.{u} D] [Small.{u} E] (F : DGFunctor A Dᵒᵖ Eᵒᵖ)

omit [Small.{u} D] in
lemma moduleRestriction_naturality {M N : ModuleCategory A E} (f : M ⟶ N)
    (x y : Dᵒᵖ) :
    (restrictModule A D E F (ForgetEnrichment.to (Complex A) M)).map x y ≫
      homPostcompose ((ForgetEnrichment.to (Complex A) M).obj (F.obj x))
        ((moduleEvaluation A E (F.obj y).unop).map f) =
    (restrictModule A D E F (ForgetEnrichment.to (Complex A) N)).map x y ≫
      homPrecompose ((moduleEvaluation A E (F.obj x).unop).map f)
        ((ForgetEnrichment.to (Complex A) N).obj (F.obj y)) := by
  have h := closedTransApp_naturality A (moduleClosedHomEquiv A E M N f) (F.obj x) (F.obj y)
  have hh := congrArg (fun k => F.map x y ≫ k) h
  exact (Category.assoc _ _ _).trans (hh.trans (Category.assoc _ _ _).symm)

def moduleRestrictionMap {M N : ModuleCategory A E} (f : M ⟶ N) :
    ForgetEnrichment.of (Complex A) (restrictModule A D E F (ForgetEnrichment.to (Complex A) M)) ⟶
      ForgetEnrichment.of (Complex A)
        (restrictModule A D E F (ForgetEnrichment.to (Complex A) N)) :=
  moduleMorphismMk A D
    (M := restrictModule A D E F (ForgetEnrichment.to (Complex A) M))
    (N := restrictModule A D E F (ForgetEnrichment.to (Complex A) N))
    (fun x => (moduleEvaluation A E (F.obj x).unop).map f)
    (moduleRestriction_naturality A D E F f)

@[simp]
lemma moduleRestrictionMap_eval {M N : ModuleCategory A E} (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).map (moduleRestrictionMap A D E F f) =
      (moduleEvaluation A E (F.obj (op x)).unop).map f :=
  moduleMorphismMk_eval A D _ _ x

/-- 閉零射にも全Hom自然性を課した主加群圏間の制限関手。 -/
def moduleRestriction : ModuleCategory A E ⥤ ModuleCategory A D where
  obj M := ForgetEnrichment.of (Complex A)
    (restrictModule A D E F (ForgetEnrichment.to (Complex A) M))
  map f := moduleRestrictionMap A D E F f
  map_id M := by
    apply moduleMorphism_ext
    intro x
    rw [moduleRestrictionMap_eval, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    apply moduleMorphism_ext
    intro x
    rw [moduleRestrictionMap_eval, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      moduleRestrictionMap_eval, moduleRestrictionMap_eval]

@[simp]
lemma moduleRestriction_map_eval {M N : ModuleCategory A E} (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).map ((moduleRestriction A D E F).map f) =
      (moduleEvaluation A E (F.obj (op x)).unop).map f :=
  moduleRestrictionMap_eval A D E F f x

def moduleRestrictionEvaluationIso (x : D) :
    moduleRestriction A D E F ⋙ moduleEvaluation A D x ≅
      moduleEvaluation A E (F.obj (op x)).unop :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact moduleRestriction_map_eval A D E F f x)

lemma moduleRestriction_map_zero (M N : ModuleCategory A E) :
    (moduleRestriction A D E F).map (0 : M ⟶ N) = 0 := by
  apply moduleMorphism_ext
  intro x
  rw [moduleRestriction_map_eval, CategoryTheory.Functor.map_zero, CategoryTheory.Functor.map_zero]

lemma moduleRestriction_quasiIso {M N : ModuleCategory A E} (f : M ⟶ N)
    (hf : moduleQuasiIso A E f) : moduleQuasiIso A D ((moduleRestriction A D E F).map f) := by
  intro x
  rw [moduleRestriction_map_eval]
  exact hf (F.obj (op x)).unop

end SerrePositivity.DifferentialGraded
end

end Restriction

/-! ## RestrictionAction（旧 SerrePositivity/DifferentialGraded/Module/RestrictionAction.lean） -/

/-! # 制限加群と代表加群の作用の成分式

## 概要
制限加群と代表加群の作用の成分式。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Bimodule/RestrictedRepresentableAction.lean。dg加群の導来作用・
準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section RestrictionAction
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] {D : Type v} {E : Type w}
  [DGCategory A D] [DGCategory A E]

lemma restrictModule_action (F : DGFunctor A Dᵒᵖ Eᵒᵖ) (M : RightModule A E)
    {x y : Dᵒᵖ} {p i n : ℤ} (f : GradedHom A x y p) (v : (M.obj (F.obj x)).X i)
    (hn : i + p = n) :
    moduleAction A (restrictModule A D E F M) f v hn =
      moduleAction A M ((F.map x y).f p f) v hn := rfl

omit [DGCategory A E] in
lemma representable_action (z : D) {x y : Dᵒᵖ} {p i n : ℤ}
    (f : GradedHom A x y p) (v : GradedHom A x.unop z i) (hn : i + p = n) :
    moduleAction A (representable A z) f v hn =
      forward A (x := y.unop) (y := x.unop) (z := z) f v (by omega) := rfl

omit [DGCategory A E] in
lemma moduleAction_units_smul (M : RightModule A D) {x y : Dᵒᵖ} {p i n : ℤ}
    (f : GradedHom A x y p) (v : (M.obj x).X i) (hn : i + p = n) (a : ℤˣ) :
    moduleAction A M f (a • v) hn = a • moduleAction A M f v hn := by
  simp only [moduleAction, Units.smul_def, map_zsmul]

end SerrePositivity.DifferentialGraded
end

end RestrictionAction

/-! ## RestrictionEnriched（旧 SerrePositivity/DifferentialGraded/Module/RestrictionEnriched.lean） -/

/-! # dg関手に沿う制限のHom複体上の構成

## 概要
dg関手に沿う制限のHom複体上の構成。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section RestrictionEnriched
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [DGCategory A E] (F : DGFunctor A Dᵒᵖ Eᵒᵖ)

/-- 任意パラメータの全次数自然変換をdg関手に沿って引き戻す。 -/
def moduleRestrictionParam {K : Complex A} {M N : RightModule A E}
    (τ : GradedNatTrans ((Center.ofBraided (Complex A)).obj K) M.toFunctor N.toFunctor) :
    GradedNatTrans ((Center.ofBraided (Complex A)).obj K)
      (restrictModule A D E F M).toFunctor (restrictModule A D E F N).toFunctor where
  app x := τ.app (F.obj x)
  naturality x y := by
    change (β_ K (x ⟶[Complex A] y)).hom ≫
      ((F.map x y ≫ M.map (F.obj x) (F.obj y)) ⊗ₘ τ.app (F.obj y)) ≫
        enrichedComposition _ _ _ =
      (τ.app (F.obj x) ⊗ₘ (F.map x y ≫ N.map (F.obj x) (F.obj y))) ≫
        enrichedComposition _ _ _
    have h := congrArg (fun t => (𝟙 K ⊗ₘ F.map x y) ≫ t)
      (τ.naturality (F.obj x) (F.obj y))
    change (𝟙 K ⊗ₘ F.map x y) ≫ (β_ K _).hom ≫
      (M.map (F.obj x) (F.obj y) ⊗ₘ τ.app (F.obj y)) ≫ enrichedComposition _ _ _ =
      (𝟙 K ⊗ₘ F.map x y) ≫ (τ.app (F.obj x) ⊗ₘ N.map (F.obj x) (F.obj y)) ≫
        enrichedComposition _ _ _ at h
    rw [BraidedCategory.braiding_naturality_assoc] at h
    simpa only [tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id] using h

variable [Small.{u} D] [Small.{u} E]

/-- 主Hom endから制限後の主Hom endへのchain map。 -/
def moduleRestrictionHom (M N : RightModule A E) :
    moduleHom A E M N ⟶ moduleHom A D (restrictModule A D E F M)
      (restrictModule A D E F N) :=
  (moduleHomEquiv A D _ _ _).symm
    (moduleRestrictionParam A D E F ((moduleHomEquiv A E _ M N) (𝟙 _)))

@[reassoc] lemma moduleRestrictionHom_π (M N : RightModule A E) (d : D) :
    moduleRestrictionHom A D E F M N ≫ moduleHomπ A D _ _ d =
      moduleHomπ A E M N (F.obj (op d)).unop := by
  rw [moduleRestrictionHom, moduleHomEquiv_symm_π]
  change 𝟙 _ ≫ moduleHomπ A E M N (F.obj (op d)).unop = _
  exact Category.id_comp _

lemma moduleRestrictionHom_identity (M : RightModule A E) :
    moduleIdentity A E M ≫ moduleRestrictionHom A D E F M M =
      moduleIdentity A D (restrictModule A D E F M) := by
  apply moduleHom_ext
  intro d
  rw [Category.assoc, moduleRestrictionHom_π, moduleIdentity_π, moduleIdentity_π]
  rfl

lemma moduleRestrictionHom_comp (M N P : RightModule A E) :
    moduleComposition A E M N P ≫ moduleRestrictionHom A D E F M P =
      (moduleRestrictionHom A D E F M N ⊗ₘ moduleRestrictionHom A D E F N P) ≫
        moduleComposition A D (restrictModule A D E F M) (restrictModule A D E F N)
          (restrictModule A D E F P) := by
  apply moduleHom_ext
  intro d
  simp only [Category.assoc, moduleRestrictionHom_π, moduleComposition_π]
  rw [tensorHom_comp_tensorHom_assoc, moduleRestrictionHom_π, moduleRestrictionHom_π]
  rfl

/-- 前合成による全次数Hom上のdg制限関手。 -/
def dgModuleRestriction : DGFunctor A (RightModule A E) (RightModule A D) where
  obj M := restrictModule A D E F M
  map M N := moduleRestrictionHom A D E F M N
  map_id := moduleRestrictionHom_identity A D E F
  map_comp := moduleRestrictionHom_comp A D E F

lemma dgModuleRestriction_map_eval {M N : ModuleCategory A E} (f : M ⟶ N) (d : D) :
    (moduleEvaluation A D d).map ((dgModuleRestriction A D E F).onClosed.map f) =
      (moduleEvaluation A E (F.obj (op d)).unop).map f := by
  apply CochainComplex.HomComplex.Cochain.ofHom_injective
  rw [moduleEvaluation_cochain, moduleEvaluation_cochain]
  change (moduleHomπ A D _ _ d).f 0
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f ≫
      moduleRestrictionHom A D E F _ _)).val = _
  rw [cycleFromUnit_postcomp]
  exact congrArg (fun k => k.f 0 (cycleFromUnit _
    (ForgetEnrichment.homTo (Complex A) f)).val)
    (moduleRestrictionHom_π A D E F (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N) d)

lemma dgModuleRestriction_map {M N : ModuleCategory A E} (f : M ⟶ N) :
    (dgModuleRestriction A D E F).onClosed.map f = (moduleRestriction A D E F).map f := by
  apply moduleMorphism_ext
  intro d
  rw [dgModuleRestriction_map_eval, moduleRestriction_map_eval]

lemma dgModuleRestriction_onClosed_eq :
    (dgModuleRestriction A D E F).onClosed = moduleRestriction A D E F := by
  apply CategoryTheory.Functor.ext
  swap
  · intro M
    rfl
  · intro M N f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact dgModuleRestriction_map A D E F f

end SerrePositivity.DifferentialGraded
end

end RestrictionEnriched

/-! ## ConeLift（旧 SerrePositivity/DifferentialGraded/Module/ConeLift.lean） -/

/-! # 全次数Homのcone比較から得られるconeへのlift -/

@[expose] public section ConeLift
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleConeLiftElement {T M N : ModuleCategory A D} (f : M ⟶ N) (q : ℤ)
    (a : (moduleHom A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) M)).X (q + 1))
    (b : (moduleHom A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) N)).X q) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).X q :=
  (moduleHomConeComparison A D T f).f q
    (complexConeElementMk A (eHomWhiskerLeft (Complex A) T f) q a b)

lemma moduleConeLiftElement_π {T M N : ModuleCategory A D} (f : M ⟶ N) (q : ℤ)
    (a) (b) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f)) x).f q
        (moduleConeLiftElement A D (T := T) f q a b) =
      mappingCone.liftCochain ((moduleEvaluation A D x).map f)
        ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
          (ForgetEnrichment.to (Complex A) M) x).f (q + 1) a)
        ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
          (ForgetEnrichment.to (Complex A) N) x).f q b) rfl := by
  rw [moduleConeLiftElement, moduleHomConeComparison_apply_π,
    complexConeElementMk_fst, complexConeElementMk_snd]

lemma moduleConeLift_cycle_eval {T M N : ModuleCategory A D} (f : M ⟶ N) (a) (b)
    (ha : (moduleHom A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) M)).d 1 2 a = 0)
    (hb : (moduleHom A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) N)).d 0 1 b +
        (show (moduleHom A D (ForgetEnrichment.to (Complex A) T)
          (ForgetEnrichment.to (Complex A) N)).X 1 from
          (eHomWhiskerLeft (Complex A) T f).f 1 a) = 0) (x : D) :
    δ 1 2 ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) M) x).f 1 a) = 0 ∧
    δ 0 1 ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) N) x).f 0 b) +
        (show Cochain ((ForgetEnrichment.to (Complex A) T).obj (Opposite.op x))
          ((ForgetEnrichment.to (Complex A) N).obj (Opposite.op x)) 1 from
          ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
            (ForgetEnrichment.to (Complex A) M) x).f 1 a).comp
            (Cochain.ofHom ((moduleEvaluation A D x).map f)) (add_zero 1)) = 0 := by
  constructor
  · have h := congrArg ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) M) x).f 2) ha
    rw [moduleHomElement_d_π, map_zero] at h
    exact h
  · have h := congrArg ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) N) x).f 1) hb
    rw [map_add, moduleHomElement_d_π, moduleHomWhiskerLeft_apply_π, map_zero] at h
    exact h

lemma moduleConeLiftElement_closed {T M N : ModuleCategory A D} (f : M ⟶ N) (a) (b)
    (ha : (moduleHom A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) M)).d 1 2 a = 0)
    (hb : (moduleHom A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) N)).d 0 1 b +
        (show (moduleHom A D (ForgetEnrichment.to (Complex A) T)
          (ForgetEnrichment.to (Complex A) N)).X 1 from
          (eHomWhiskerLeft (Complex A) T f).f 1 a) = 0) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).d 0 1
        (moduleConeLiftElement A D (T := T) f 0 a b) = 0 := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomElement_d_π, moduleConeLiftElement_π, map_zero]
  have hx := moduleConeLift_cycle_eval A D (T := T) f a b ha hb x
  exact Cocycle.δ_eq_zero
    (mappingCone.liftCocycle ((moduleEvaluation A D x).map f)
      (Cocycle.mk ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
        (ForgetEnrichment.to (Complex A) M) x).f 1 a) 2 rfl hx.1)
      ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
        (ForgetEnrichment.to (Complex A) N) x).f 0 b) (zero_add 1) hx.2) 1

def moduleConeLiftOfCycle {T M N : ModuleCategory A D} (f : M ⟶ N) (a) (b)
    (ha : (moduleHom A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) M)).d 1 2 a = 0)
    (hb : (moduleHom A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) N)).d 0 1 b +
        (show (moduleHom A D (ForgetEnrichment.to (Complex A) T)
          (ForgetEnrichment.to (Complex A) N)).X 1 from
          (eHomWhiskerLeft (Complex A) T f).f 1 a) = 0) : T ⟶ moduleCone A D f :=
  moduleMorphismOfCycle A D (moduleConeLiftElement A D f 0 a b)
    (moduleConeLiftElement_closed A D f a b ha hb)

@[simp] lemma moduleConeLiftOfCycle_eval {T M N : ModuleCategory A D} (f : M ⟶ N)
    (a) (b) (ha) (hb) (x : D) :
    (moduleEvaluation A D x).map (moduleConeLiftOfCycle A D (T := T) f a b ha hb) =
      mappingCone.lift ((moduleEvaluation A D x).map f)
        (Cocycle.mk ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
          (ForgetEnrichment.to (Complex A) M) x).f 1 a) 2 rfl
          (moduleConeLift_cycle_eval A D f a b ha hb x).1)
        ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
          (ForgetEnrichment.to (Complex A) N) x).f 0 b)
        (moduleConeLift_cycle_eval A D f a b ha hb x).2 := by
  apply Cochain.ofHom_injective
  rw [moduleEvaluation_cochain, mappingCone.ofHom_lift]
  change (moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
    (ForgetEnrichment.to (Complex A) (moduleCone A D f)) x).f 0
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (moduleMorphismOfCycle A D (moduleConeLiftElement A D f 0 a b) _))).val = _
  rw [moduleMorphismOfCycle_cycle, moduleConeLiftElement_π]
  rfl

end SerrePositivity.DifferentialGraded
end

end ConeLift

/-! ## ConeHomotopyDesc（旧 SerrePositivity/DifferentialGraded/Module/ConeHomotopyDesc.lean） -/

/-! # 全dg自然なホモトピーを用いるconeからの延長

通常順の斉次合成でconeの二つの射影を組み合わせる。
-/

@[expose] public section ConeHomotopyDesc
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- coneからの閉零射の候補。hは次数−1、bは閉零射。 -/
def moduleConeDescElement {L M T : ModuleCategory A D} (a : L ⟶ M)
    (h : (moduleHom A D (ForgetEnrichment.to (Complex A) L)
      (ForgetEnrichment.to (Complex A) T)).X (-1)) (b : M ⟶ T) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D a))
      (ForgetEnrichment.to (Complex A) T)).X 0 :=
  compose A (x := ForgetEnrichment.to (Complex A) (moduleCone A D a))
    (y := ForgetEnrichment.to (Complex A) L) (z := ForgetEnrichment.to (Complex A) T)
    h (moduleConeFstElement A D a) (by omega) +
  compose A (x := ForgetEnrichment.to (Complex A) (moduleCone A D a))
    (y := ForgetEnrichment.to (Complex A) M) (z := ForgetEnrichment.to (Complex A) T)
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) b)).val
    (moduleConeSndElement A D a) (by omega)

lemma moduleConeDescElement_π {L M T : ModuleCategory A D} (a : L ⟶ M) (h) (b : M ⟶ T)
    (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) (moduleCone A D a))
      (ForgetEnrichment.to (Complex A) T) x).f 0 (moduleConeDescElement A D a h b) =
      mappingCone.descCochain ((moduleEvaluation A D x).map a)
        ((moduleHomπ A D (ForgetEnrichment.to (Complex A) L)
          (ForgetEnrichment.to (Complex A) T) x).f (-1) h)
        (Cochain.ofHom ((moduleEvaluation A D x).map b)) (by omega) := by
  rw [moduleConeDescElement, map_add, moduleHomCompose_π, moduleHomCompose_π,
    moduleConeFstElement_π, moduleConeSndElement_π, ← moduleEvaluation_cochain]
  rfl

lemma moduleConeDescElement_closed {L M T : ModuleCategory A D} (a : L ⟶ M) (h) (b : M ⟶ T)
    (hh : (moduleHom A D (ForgetEnrichment.to (Complex A) L)
      (ForgetEnrichment.to (Complex A) T)).d (-1) 0 h =
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (a ≫ b))).val) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D a))
      (ForgetEnrichment.to (Complex A) T)).d 0 1 (moduleConeDescElement A D a h b) = 0 := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomElement_d_π, moduleConeDescElement_π, map_zero,
    mappingCone.δ_descCochain _ _ _ _ 1 (by omega)]
  have hc := congrArg ((moduleHomπ A D (ForgetEnrichment.to (Complex A) L)
    (ForgetEnrichment.to (Complex A) T) x).f 0) hh
  rw [moduleHomElement_d_π, ← moduleEvaluation_cochain,
    CategoryTheory.Functor.map_comp, Cochain.ofHom_comp] at hc
  rw [hc]
  simp

/-- hの境界がa≫bなら、cone(a)→Tを構成できる。 -/
def moduleConeDescOfBoundary {L M T : ModuleCategory A D} (a : L ⟶ M) (h) (b : M ⟶ T)
    (hh : (moduleHom A D (ForgetEnrichment.to (Complex A) L)
      (ForgetEnrichment.to (Complex A) T)).d (-1) 0 h =
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (a ≫ b))).val) :
    moduleCone A D a ⟶ T :=
  moduleMorphismOfCycle A D (moduleConeDescElement A D a h b)
    (moduleConeDescElement_closed A D a h b hh)


lemma moduleConeDescBoundary_condition_eval {L M T : ModuleCategory A D} (a : L ⟶ M)
    (h) (b : M ⟶ T)
    (hh : (moduleHom A D (ForgetEnrichment.to (Complex A) L)
      (ForgetEnrichment.to (Complex A) T)).d (-1) 0 h =
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (a ≫ b))).val) (x : D) :
    δ (-1) 0 ((moduleHomπ A D (ForgetEnrichment.to (Complex A) L)
      (ForgetEnrichment.to (Complex A) T) x).f (-1) h) =
        Cochain.ofHom ((moduleEvaluation A D x).map a ≫ (moduleEvaluation A D x).map b) := by
  have hc := congrArg ((moduleHomπ A D (ForgetEnrichment.to (Complex A) L)
    (ForgetEnrichment.to (Complex A) T) x).f 0) hh
  rw [moduleHomElement_d_π, ← moduleEvaluation_cochain,
    CategoryTheory.Functor.map_comp] at hc
  exact hc

@[simp] lemma moduleConeDescOfBoundary_eval {L M T : ModuleCategory A D} (a : L ⟶ M)
    (h) (b : M ⟶ T) (hh) (x : D) :
    (moduleEvaluation A D x).map (moduleConeDescOfBoundary A D a h b hh) =
      mappingCone.desc ((moduleEvaluation A D x).map a)
        ((moduleHomπ A D (ForgetEnrichment.to (Complex A) L)
          (ForgetEnrichment.to (Complex A) T) x).f (-1) h)
        ((moduleEvaluation A D x).map b)
        (moduleConeDescBoundary_condition_eval A D a h b hh x) := by
  apply Cochain.ofHom_injective
  rw [moduleEvaluation_cochain, mappingCone.ofHom_desc]
  change (moduleHomπ A D (ForgetEnrichment.to (Complex A) (moduleCone A D a))
    (ForgetEnrichment.to (Complex A) T) x).f 0
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (moduleMorphismOfCycle A D (moduleConeDescElement A D a h b) _))).val = _
  rw [moduleMorphismOfCycle_cycle, moduleConeDescElement_π]

@[reassoc] lemma moduleConeDescOfBoundary_inr {L M T : ModuleCategory A D} (a : L ⟶ M)
    (h) (b : M ⟶ T) (hh) :
    moduleConeInr A D a ≫ moduleConeDescOfBoundary A D a h b hh = b := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, moduleConeInr_eval, moduleConeDescOfBoundary_eval]
  exact mappingCone.inr_desc _ _ _ _

end SerrePositivity.DifferentialGraded
end

end ConeHomotopyDesc

/-! ## ConeShiftElements（旧 SerrePositivity/DifferentialGraded/Module/ConeShiftElements.lean） -/

/-! # cone shift比較射の全dg自然な入力 -/

@[expose] public section ConeShiftElements
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleConeShiftFirst (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (shiftModule s (ForgetEnrichment.to (Complex A) (moduleCone A D f)))
      (shiftModule s (ForgetEnrichment.to (Complex A) M))).X 1 :=
  (moduleShiftHom A D s _ _).f 1 (moduleConeFstElement A D f)

def moduleConeShiftSecond (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (shiftModule s (ForgetEnrichment.to (Complex A) (moduleCone A D f)))
      (shiftModule s (ForgetEnrichment.to (Complex A) N))).X 0 :=
  (moduleShiftHom A D s _ _).f 0 (moduleConeSndElement A D f)

def moduleConeShiftLeftInput (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (shiftModule s (ForgetEnrichment.to (Complex A) M))
      (shiftModule s (ForgetEnrichment.to (Complex A) (moduleCone A D f)))).X (-1) :=
  (moduleShiftHom A D s _ _).f (-1) (moduleConeInlElement A D f)

lemma moduleConeShiftFirst_π (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleHomπ A D (shiftModule s (ForgetEnrichment.to (Complex A) (moduleCone A D f)))
      (shiftModule s (ForgetEnrichment.to (Complex A) M)) x).f 1 (moduleConeShiftFirst A D s f) =
        s.negOnePow • (mappingCone.fst ((moduleEvaluation A D x).map f)).val.shift s := by
  have h := moduleShiftHomElement_π A D s 1 (moduleConeFstElement A D f) x
  rw [moduleConeFstElement_π, mul_one] at h
  exact h

lemma moduleConeShiftSecond_π (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleHomπ A D (shiftModule s (ForgetEnrichment.to (Complex A) (moduleCone A D f)))
      (shiftModule s (ForgetEnrichment.to (Complex A) N)) x).f 0 (moduleConeShiftSecond A D s f) =
        (mappingCone.snd ((moduleEvaluation A D x).map f)).shift s := by
  have h := moduleShiftHomElement_π A D s 0 (moduleConeSndElement A D f) x
  rw [moduleConeSndElement_π, mul_zero, Int.negOnePow_zero, one_smul] at h
  exact h

lemma moduleConeShiftLeftInput_π (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleHomπ A D (shiftModule s (ForgetEnrichment.to (Complex A) M))
      (shiftModule s (ForgetEnrichment.to (Complex A) (moduleCone A D f))) x).f (-1)
        (moduleConeShiftLeftInput A D s f) =
      s.negOnePow • (mappingCone.inl ((moduleEvaluation A D x).map f)).shift s := by
  have h := moduleShiftHomElement_π A D s (-1) (moduleConeInlElement A D f) x
  rw [moduleConeInlElement_π, mul_neg_one, Int.negOnePow_neg] at h
  exact h

lemma moduleConeShiftFirst_closed (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (shiftModule s (ForgetEnrichment.to (Complex A) (moduleCone A D f)))
      (shiftModule s (ForgetEnrichment.to (Complex A) M))).d 1 2
        (moduleConeShiftFirst A D s f) = 0 := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomElement_d_π, moduleConeShiftFirst_π, map_zero]
  exact Cocycle.δ_eq_zero
    (s.negOnePow • (mappingCone.fst ((moduleEvaluation A D x).map f)).shift s) 2

lemma moduleConeShiftInputs_cycle (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (shiftModule s (ForgetEnrichment.to (Complex A) (moduleCone A D f)))
      (shiftModule s (ForgetEnrichment.to (Complex A) N))).d 0 1 (moduleConeShiftSecond A D s f) +
      (show (moduleHom A D (shiftModule s (ForgetEnrichment.to (Complex A) (moduleCone A D f)))
        (shiftModule s (ForgetEnrichment.to (Complex A) N))).X 1 from
        (eHomWhiskerLeft (Complex A) (moduleShiftObj A D s (moduleCone A D f))
          (moduleShiftMap A D s f)).f 1 (moduleConeShiftFirst A D s f)) = 0 := by
  apply moduleHomElement_ext A D
  intro x
  rw [map_add, moduleHomElement_d_π, moduleConeShiftSecond_π, map_zero]
  have hp := moduleHomWhiskerLeft_apply_π A D
    (T := moduleShiftObj A D s (moduleCone A D f)) (moduleShiftMap A D s f) 1
    (moduleConeShiftFirst A D s f) x
  have hfirst := moduleConeShiftFirst_π A D s f x
  have hp' := hp.trans (congrArg
    (fun z => z.comp (Cochain.ofHom ((moduleEvaluation A D x).map (moduleShiftMap A D s f)))
      (add_zero 1)) hfirst)
  exact (congrArg
    (fun z : Cochain ((mappingCone ((moduleEvaluation A D x).map f))⟦s⟧)
      (((moduleEvaluation A D x).obj N)⟦s⟧) 1 =>
        δ 0 1 ((mappingCone.snd ((moduleEvaluation A D x).map f)).shift s) + z) hp').trans
    (complexConeShift_lift_condition _ _ _ (moduleShiftMap_eval A D s f x))

lemma moduleConeShiftLeftInput_d (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (shiftModule s (ForgetEnrichment.to (Complex A) M))
      (shiftModule s (ForgetEnrichment.to (Complex A) (moduleCone A D f)))).d (-1) 0
        (moduleConeShiftLeftInput A D s f) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (moduleShiftMap A D s f ≫ moduleShiftMap A D s (moduleConeInr A D f)))).val := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomElement_d_π, moduleConeShiftLeftInput_π]
  have he := moduleEvaluation_cochain A D x
    (moduleShiftMap A D s f ≫ moduleShiftMap A D s (moduleConeInr A D f))
  rw [CategoryTheory.Functor.map_comp, moduleShiftMap_eval A D s (moduleConeInr A D f) x,
    moduleConeInr_eval A D f x] at he
  exact (complexConeShift_desc_condition _ _ _ (moduleShiftMap_eval A D s f x)).trans he

end SerrePositivity.DifferentialGraded
end

end ConeShiftElements

/-! ## ConeShift（旧 SerrePositivity/DifferentialGraded/Module/ConeShift.lean） -/

/-! # 加群圏でのconeと整数shiftの同型 -/

@[expose] public section ConeShift
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleConeShiftHom (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleShiftObj A D s (moduleCone A D f) ⟶ moduleCone A D (moduleShiftMap A D s f) :=
  moduleConeLiftOfCycle A D (moduleShiftMap A D s f)
    (moduleConeShiftFirst A D s f) (moduleConeShiftSecond A D s f)
    (moduleConeShiftFirst_closed A D s f) (moduleConeShiftInputs_cycle A D s f)

def moduleConeShiftInv (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleCone A D (moduleShiftMap A D s f) ⟶ moduleShiftObj A D s (moduleCone A D f) :=
  moduleConeDescOfBoundary A D (moduleShiftMap A D s f) (moduleConeShiftLeftInput A D s f)
    (moduleShiftMap A D s (moduleConeInr A D f)) (moduleConeShiftLeftInput_d A D s f)

@[simp] lemma moduleConeShiftHom_eval (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).map (moduleConeShiftHom A D s f) =
      (complexConeShiftIso ((moduleEvaluation A D x).map f) s
        ((moduleEvaluation A D x).map (moduleShiftMap A D s f))
        (moduleShiftMap_eval A D s f x)).hom := by
  unfold moduleConeShiftHom
  rw [moduleConeLiftOfCycle_eval]
  apply Cochain.ofHom_injective
  rw [mappingCone.ofHom_lift, complexConeShiftIso_hom_cochain]
  change mappingCone.liftCochain ((moduleEvaluation A D x).map (moduleShiftMap A D s f))
    ((moduleHomπ A D (shiftModule s (ForgetEnrichment.to (Complex A) (moduleCone A D f)))
      (shiftModule s (ForgetEnrichment.to (Complex A) M)) x).f 1 (moduleConeShiftFirst A D s f))
    ((moduleHomπ A D (shiftModule s (ForgetEnrichment.to (Complex A) (moduleCone A D f)))
      (shiftModule s (ForgetEnrichment.to (Complex A) N)) x).f 0 (moduleConeShiftSecond A D s f))
    (zero_add 1) = _
  rw [moduleConeShiftFirst_π, moduleConeShiftSecond_π]

@[simp] lemma moduleConeShiftInv_eval (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).map (moduleConeShiftInv A D s f) =
      (complexConeShiftIso ((moduleEvaluation A D x).map f) s
        ((moduleEvaluation A D x).map (moduleShiftMap A D s f))
        (moduleShiftMap_eval A D s f x)).inv := by
  unfold moduleConeShiftInv
  rw [moduleConeDescOfBoundary_eval]
  apply Cochain.ofHom_injective
  rw [mappingCone.ofHom_desc, complexConeShiftIso_inv_cochain]
  change mappingCone.descCochain ((moduleEvaluation A D x).map (moduleShiftMap A D s f))
    ((moduleHomπ A D (shiftModule s (ForgetEnrichment.to (Complex A) M))
      (shiftModule s (ForgetEnrichment.to (Complex A) (moduleCone A D f))) x).f (-1)
        (moduleConeShiftLeftInput A D s f))
    (Cochain.ofHom ((moduleEvaluation A D x).map (moduleShiftMap A D s (moduleConeInr A D f))))
    (neg_add_cancel 1) = _
  rw [moduleConeShiftLeftInput_π, moduleShiftMap_eval A D s (moduleConeInr A D f) x,
    moduleConeInr_eval A D f x]

lemma moduleConeShift_hom_inv (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleConeShiftHom A D s f ≫ moduleConeShiftInv A D s f = 𝟙 _ := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, moduleConeShiftHom_eval, moduleConeShiftInv_eval,
    CategoryTheory.Functor.map_id, Iso.hom_inv_id]

lemma moduleConeShift_inv_hom (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleConeShiftInv A D s f ≫ moduleConeShiftHom A D s f = 𝟙 _ := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, moduleConeShiftInv_eval, moduleConeShiftHom_eval,
    CategoryTheory.Functor.map_id, Iso.inv_hom_id]

/-- 非有界dg加群のconeと任意整数shiftの、実際の加群圏での同型。 -/
def moduleConeShiftIso (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleShiftObj A D s (moduleCone A D f) ≅ moduleCone A D (moduleShiftMap A D s f) where
  hom := moduleConeShiftHom A D s f
  inv := moduleConeShiftInv A D s f
  hom_inv_id := moduleConeShift_hom_inv A D s f
  inv_hom_id := moduleConeShift_inv_hom A D s f

end SerrePositivity.DifferentialGraded
end

end ConeShift

/-! ## ConeElementRelations（旧 SerrePositivity/DifferentialGraded/Module/ConeElementRelations.lean） -/

/-! # 主Hom endにおける標準coneの行列恒等式 -/

@[expose] public section ConeElementRelations
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

def moduleConeInrElement (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).X 0 :=
  (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (moduleConeInr A D f))).val

lemma moduleConeInrElement_π (f : M ⟶ N) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f)) x).f 0 (moduleConeInrElement A D f) =
      Cochain.ofHom (mappingCone.inr ((moduleEvaluation A D x).map f)) := by
  rw [moduleConeInrElement, ← moduleEvaluation_cochain, moduleConeInr_eval]

lemma moduleCone_inl_fst (f : M ⟶ N) :
    compose A (moduleConeFstElement A D f) (moduleConeInlElement A D f) (neg_add_cancel 1) =
      (unitElement A (ForgetEnrichment.to (Complex A) M)).val := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomCompose_π, moduleConeInlElement_π, moduleConeFstElement_π, yoneda_moduleUnit_π]
  exact mappingCone.inl_fst _

lemma moduleCone_inl_snd (f : M ⟶ N) :
    compose A (x := ForgetEnrichment.to (Complex A) M)
      (y := ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (z := ForgetEnrichment.to (Complex A) N)
      (moduleConeSndElement A D f) (moduleConeInlElement A D f) (add_zero (-1)) = 0 := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomCompose_π, moduleConeInlElement_π, moduleConeSndElement_π, map_zero]
  exact mappingCone.inl_snd _

lemma moduleCone_inr_fst (f : M ⟶ N) :
    compose A (x := ForgetEnrichment.to (Complex A) N)
      (y := ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (z := ForgetEnrichment.to (Complex A) M)
      (moduleConeFstElement A D f) (moduleConeInrElement A D f) (zero_add 1) = 0 := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomCompose_π, moduleConeInrElement_π, moduleConeFstElement_π, map_zero]
  exact mappingCone.inr_fst _

lemma moduleCone_inr_snd (f : M ⟶ N) :
    compose A (moduleConeSndElement A D f) (moduleConeInrElement A D f) (zero_add 0) =
      (unitElement A (ForgetEnrichment.to (Complex A) N)).val := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomCompose_π, moduleConeInrElement_π, moduleConeSndElement_π, yoneda_moduleUnit_π]
  exact mappingCone.inr_snd _

lemma moduleCone_decomposition (f : M ⟶ N) :
    compose A (moduleConeInlElement A D f) (moduleConeFstElement A D f) (add_neg_cancel 1) +
      compose A (moduleConeInrElement A D f) (moduleConeSndElement A D f) (add_zero 0) =
      (unitElement A (ForgetEnrichment.to (Complex A) (moduleCone A D f))).val := by
  apply moduleHomElement_ext A D
  intro x
  rw [map_add, moduleHomCompose_π, moduleHomCompose_π, moduleConeInlElement_π,
    moduleConeFstElement_π, moduleConeSndElement_π, moduleConeInrElement_π, yoneda_moduleUnit_π]
  apply Cochain.ext₀
  intro n
  rw [Cochain.add_v, Cochain.comp_v _ _ _ n (n + 1) n rfl (by omega)]
  simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, HomologicalComplex.id_f]
  apply mappingCone.ext_to ((moduleEvaluation A D x).map f) n (n + 1) rfl <;>
    simp [Preadditive.add_comp, Category.assoc]

end SerrePositivity.DifferentialGraded
end

end ConeElementRelations

/-! ## ConeCompositionInputs（旧 SerrePositivity/DifferentialGraded/Module/ConeCompositionInputs.lean） -/

/-! # 合成coneの比較射に用いる全dg自然な入力 -/

@[expose] public section ConeCompositionInputs
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 合成f≫gによる標準cone射cone(f)→cone(f≫g)。 -/
def moduleConeCompMap {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    moduleCone A D f ⟶ moduleCone A D (f ≫ g) :=
  moduleConeMap A D f (f ≫ g) (𝟙 M) g (by simp)

lemma moduleConeCompMap_eval {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P)
    (x : D) :
    (moduleEvaluation A D x).map (moduleConeCompMap A D f g) =
      mappingCone.map ((moduleEvaluation A D x).map f) ((moduleEvaluation A D x).map (f ≫ g))
        (𝟙 ((moduleEvaluation A D x).obj M)) ((moduleEvaluation A D x).map g)
        (by rw [CategoryTheory.Functor.map_comp, Category.id_comp]) := by
  unfold moduleConeCompMap
  simpa only [CategoryTheory.Functor.map_id] using
    moduleConeMap_eval A D f (f ≫ g) (𝟙 M) g (by simp) x

/-- cone(g)→cone(f)の次数1の入力。 -/
def moduleConeCompLiftFirst {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D g))
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).X 1 :=
  (eHomWhiskerLeft (Complex A) (moduleCone A D g) (moduleConeInr A D f)).f 1
    (moduleConeFstElement A D g)

/-- cone(g)→cone(f≫g)の次数0の入力。閉性は二つの入力を組み合わせて得る。 -/
def moduleConeCompLiftSecond {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D g))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (f ≫ g)))).X 0 :=
  moduleConeDescElement A D g 0 (moduleConeInr A D (f ≫ g))

lemma moduleConeCompLiftFirst_π {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P)
    (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) (moduleCone A D g))
      (ForgetEnrichment.to (Complex A) (moduleCone A D f)) x).f 1
        (moduleConeCompLiftFirst A D f g) =
      (mappingCone.fst ((moduleEvaluation A D x).map g)).val.comp
        (Cochain.ofHom (mappingCone.inr ((moduleEvaluation A D x).map f))) (add_zero 1) := by
  rw [moduleConeCompLiftFirst, moduleHomWhiskerLeft_apply_π,
    moduleConeFstElement_π, moduleConeInr_eval]

lemma moduleConeCompLiftSecond_π {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P)
    (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) (moduleCone A D g))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (f ≫ g))) x).f 0
        (moduleConeCompLiftSecond A D f g) =
      mappingCone.descCochain ((moduleEvaluation A D x).map g) 0
        (Cochain.ofHom (mappingCone.inr ((moduleEvaluation A D x).map (f ≫ g))))
        (neg_add_cancel 1) := by
  rw [moduleConeCompLiftSecond, moduleConeDescElement_π, map_zero, moduleConeInr_eval]

lemma moduleConeCompLiftFirst_closed {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D g))
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).d 1 2
        (moduleConeCompLiftFirst A D f g) = 0 := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomElement_d_π, moduleConeCompLiftFirst_π, map_zero]
  simp only [δ_comp_ofHom, Cocycle.δ_eq_zero, Cochain.zero_comp]

lemma moduleConeCompLiftInputs_cycle {M N P : ModuleCategory A D}
    (f : M ⟶ N) (g : N ⟶ P) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D g))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (f ≫ g)))).d 0 1
        (moduleConeCompLiftSecond A D f g) +
      (show (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D g))
        (ForgetEnrichment.to (Complex A) (moduleCone A D (f ≫ g)))).X 1 from
          (eHomWhiskerLeft (Complex A) (moduleCone A D g) (moduleConeCompMap A D f g)).f 1
            (moduleConeCompLiftFirst A D f g)) = 0 := by
  apply moduleHomElement_ext A D
  intro x
  rw [map_add, moduleHomElement_d_π, moduleConeCompLiftSecond_π,
    moduleHomWhiskerLeft_apply_π, moduleConeCompLiftFirst_π, map_zero]
  exact complexConeComp_inputs_cycle ((moduleEvaluation A D x).map f)
    ((moduleEvaluation A D x).map g) ((moduleEvaluation A D x).map (f ≫ g))
    ((moduleEvaluation A D x).map_comp f g)
    ((moduleEvaluation A D x).map (moduleConeCompMap A D f g))
    (moduleConeCompMap_eval A D f g x)

/-- 全dg自然なcone(g)→cone(cone(f)→cone(f≫g))の順方向比較射。 -/
def moduleConeCompHom {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    moduleCone A D g ⟶ moduleCone A D (moduleConeCompMap A D f g) :=
  moduleConeLiftOfCycle A D (moduleConeCompMap A D f g)
    (moduleConeCompLiftFirst A D f g) (moduleConeCompLiftSecond A D f g)
    (moduleConeCompLiftFirst_closed A D f g) (moduleConeCompLiftInputs_cycle A D f g)

@[simp] lemma moduleConeCompHom_eval {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P)
    (x : D) :
    (moduleEvaluation A D x).map (moduleConeCompHom A D f g) =
      (complexConeCompHomotopyEquiv ((moduleEvaluation A D x).map f)
        ((moduleEvaluation A D x).map g) ((moduleEvaluation A D x).map (f ≫ g))
        ((moduleEvaluation A D x).map_comp f g)
        ((moduleEvaluation A D x).map (moduleConeCompMap A D f g))
        (moduleConeCompMap_eval A D f g x)).hom := by
  unfold moduleConeCompHom
  rw [moduleConeLiftOfCycle_eval]
  apply Cochain.ofHom_injective
  rw [mappingCone.ofHom_lift, complexConeComp_hom_cochain]
  change mappingCone.liftCochain ((moduleEvaluation A D x).map (moduleConeCompMap A D f g))
    ((moduleHomπ A D (ForgetEnrichment.to (Complex A) (moduleCone A D g))
      (ForgetEnrichment.to (Complex A) (moduleCone A D f)) x).f 1
        (moduleConeCompLiftFirst A D f g))
    ((moduleHomπ A D (ForgetEnrichment.to (Complex A) (moduleCone A D g))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (f ≫ g))) x).f 0
        (moduleConeCompLiftSecond A D f g)) (zero_add 1) = _
  rw [moduleConeCompLiftFirst_π, moduleConeCompLiftSecond_π]

end SerrePositivity.DifferentialGraded
end

end ConeCompositionInputs

/-! ## ConeCompositionDesc（旧 SerrePositivity/DifferentialGraded/Module/ConeCompositionDesc.lean） -/

/-! # 合成cone比較の全dg自然な逆方向射 -/

@[expose] public section ConeCompositionDesc
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleConeCompInnerElement {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (moduleCone A D g))).X (-1) :=
  compose A (x := ForgetEnrichment.to (Complex A) M)
    (y := ForgetEnrichment.to (Complex A) N)
    (z := ForgetEnrichment.to (Complex A) (moduleCone A D g))
    (moduleConeInlElement A D g)
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val (zero_add (-1))

def moduleConeCompOuterElement {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) (moduleCone A D g))).X (-1) :=
  compose A (x := ForgetEnrichment.to (Complex A) (moduleCone A D f))
    (y := ForgetEnrichment.to (Complex A) N)
    (z := ForgetEnrichment.to (Complex A) (moduleCone A D g))
    (moduleConeInlElement A D g) (moduleConeSndElement A D f) (zero_add (-1))

lemma moduleConeCompInnerElement_π {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P)
    (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (moduleCone A D g)) x).f (-1)
        (moduleConeCompInnerElement A D f g) =
      (Cochain.ofHom ((moduleEvaluation A D x).map f)).comp
        (mappingCone.inl ((moduleEvaluation A D x).map g)) (zero_add (-1)) := by
  rw [moduleConeCompInnerElement, moduleHomCompose_π,
    ← moduleEvaluation_cochain, moduleConeInlElement_π]

lemma moduleConeCompOuterElement_π {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P)
    (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) (moduleCone A D g)) x).f (-1)
        (moduleConeCompOuterElement A D f g) =
      (mappingCone.snd ((moduleEvaluation A D x).map f)).comp
        (mappingCone.inl ((moduleEvaluation A D x).map g)) (zero_add (-1)) := by
  rw [moduleConeCompOuterElement, moduleHomCompose_π,
    moduleConeSndElement_π, moduleConeInlElement_π]

lemma moduleConeCompInnerElement_d {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (moduleCone A D g))).d (-1) 0
        (moduleConeCompInnerElement A D f g) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        ((f ≫ g) ≫ moduleConeInr A D g))).val := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomElement_d_π, moduleConeCompInnerElement_π, ← moduleEvaluation_cochain,
    (moduleEvaluation A D x).map_comp (f ≫ g) (moduleConeInr A D g), moduleConeInr_eval]
  exact complexConeComp_inner_boundary ((moduleEvaluation A D x).map f)
    ((moduleEvaluation A D x).map g) ((moduleEvaluation A D x).map (f ≫ g))
    ((moduleEvaluation A D x).map_comp f g)

def moduleConeCompInnerDesc {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    moduleCone A D (f ≫ g) ⟶ moduleCone A D g :=
  moduleConeDescOfBoundary A D (f ≫ g) (moduleConeCompInnerElement A D f g)
    (moduleConeInr A D g) (moduleConeCompInnerElement_d A D f g)

lemma moduleConeCompInnerDesc_cochain {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P)
    (x : D) :
    Cochain.ofHom ((moduleEvaluation A D x).map (moduleConeCompInnerDesc A D f g)) =
      mappingCone.descCochain ((moduleEvaluation A D x).map (f ≫ g))
        ((Cochain.ofHom ((moduleEvaluation A D x).map f)).comp
          (mappingCone.inl ((moduleEvaluation A D x).map g)) (zero_add (-1)))
        (Cochain.ofHom (mappingCone.inr ((moduleEvaluation A D x).map g))) (neg_add_cancel 1) := by
  unfold moduleConeCompInnerDesc
  rw [moduleConeDescOfBoundary_eval, mappingCone.ofHom_desc]
  change mappingCone.descCochain ((moduleEvaluation A D x).map (f ≫ g))
    ((moduleHomπ A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (moduleCone A D g)) x).f (-1)
        (moduleConeCompInnerElement A D f g))
    (Cochain.ofHom ((moduleEvaluation A D x).map (moduleConeInr A D g))) (neg_add_cancel 1) = _
  rw [moduleConeCompInnerElement_π, moduleConeInr_eval]

lemma moduleConeCompOuterElement_d {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) (moduleCone A D g))).d (-1) 0
        (moduleConeCompOuterElement A D f g) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (moduleConeCompMap A D f g ≫ moduleConeCompInnerDesc A D f g))).val := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomElement_d_π, moduleConeCompOuterElement_π, ← moduleEvaluation_cochain,
    (moduleEvaluation A D x).map_comp, Cochain.ofHom_comp, moduleConeCompInnerDesc_cochain]
  have h := complexConeComp_outer_boundary ((moduleEvaluation A D x).map f)
    ((moduleEvaluation A D x).map g) ((moduleEvaluation A D x).map (f ≫ g))
    ((moduleEvaluation A D x).map_comp f g)
    ((moduleEvaluation A D x).map (moduleConeCompMap A D f g)) (moduleConeCompMap_eval A D f g x)
  rw [Cochain.ofHom_comp, mappingCone.ofHom_desc] at h
  exact h

/-- cone(cone(f)→cone(f≫g))からcone(g)への全dg自然な逆方向比較。 -/
def moduleConeCompInv {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    moduleCone A D (moduleConeCompMap A D f g) ⟶ moduleCone A D g :=
  moduleConeDescOfBoundary A D (moduleConeCompMap A D f g)
    (moduleConeCompOuterElement A D f g) (moduleConeCompInnerDesc A D f g)
    (moduleConeCompOuterElement_d A D f g)

@[simp] lemma moduleConeCompInv_eval {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P)
    (x : D) :
    (moduleEvaluation A D x).map (moduleConeCompInv A D f g) =
      (complexConeCompHomotopyEquiv ((moduleEvaluation A D x).map f)
        ((moduleEvaluation A D x).map g) ((moduleEvaluation A D x).map (f ≫ g))
        ((moduleEvaluation A D x).map_comp f g)
        ((moduleEvaluation A D x).map (moduleConeCompMap A D f g))
        (moduleConeCompMap_eval A D f g x)).inv := by
  unfold moduleConeCompInv
  rw [moduleConeDescOfBoundary_eval]
  apply Cochain.ofHom_injective
  rw [mappingCone.ofHom_desc, complexConeComp_inv_cochain]
  rw [moduleConeCompOuterElement_π, moduleConeCompInnerDesc_cochain]

lemma moduleConeComp_hom_inv {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    moduleConeCompHom A D f g ≫ moduleConeCompInv A D f g = 𝟙 _ := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, moduleConeCompHom_eval, moduleConeCompInv_eval,
    complexConeComp_hom_inv, CategoryTheory.Functor.map_id]
  rfl

end SerrePositivity.DifferentialGraded
end

end ConeCompositionDesc

/-! ## ConeCompositionHomotopy（旧 SerrePositivity/DifferentialGraded/Module/ConeCompositionHomotopy.lean） -/

/-! # 合成cone比較の全dg自然な収縮とK(D)の同型 -/

@[expose] public section ConeCompositionHomotopy
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleConeCompContractingLeft {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeCompMap A D f g)))).X (-2) :=
  compose A (x := ForgetEnrichment.to (Complex A) M)
    (y := ForgetEnrichment.to (Complex A) (moduleCone A D f))
    (z := ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeCompMap A D f g)))
    (moduleConeInlElement A D (moduleConeCompMap A D f g)) (moduleConeInlElement A D f)
    (show (-1 : ℤ) + (-1) = -2 by decide)

def moduleConeCompContractingMiddle {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D (f ≫ g)))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeCompMap A D f g)))).X (-1) :=
  compose A (x := ForgetEnrichment.to (Complex A) (moduleCone A D (f ≫ g)))
    (y := ForgetEnrichment.to (Complex A) M)
    (z := ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeCompMap A D f g)))
    (moduleConeCompContractingLeft A D f g) (moduleConeFstElement A D (f ≫ g))
    (show (1 : ℤ) + (-2) = -1 by decide)

def moduleConeCompContractingElement {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeCompMap A D f g)))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeCompMap A D f g)))).X (-1) :=
  -compose A
    (x := ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeCompMap A D f g)))
    (y := ForgetEnrichment.to (Complex A) (moduleCone A D (f ≫ g)))
    (z := ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeCompMap A D f g)))
    (moduleConeCompContractingMiddle A D f g)
    (moduleConeSndElement A D (moduleConeCompMap A D f g)) (zero_add (-1))

lemma moduleConeCompContractingElement_π {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P)
    (x : D) :
    (moduleHomπ A D
      (ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeCompMap A D f g)))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeCompMap A D f g))) x).f (-1)
        (moduleConeCompContractingElement A D f g) =
      -((mappingCone.snd ((moduleEvaluation A D x).map (moduleConeCompMap A D f g))).comp
        ((mappingCone.fst ((moduleEvaluation A D x).map (f ≫ g))).val.comp
          ((mappingCone.inl ((moduleEvaluation A D x).map f)).comp
            (mappingCone.inl ((moduleEvaluation A D x).map (moduleConeCompMap A D f g)))
            (show (-1 : ℤ) + (-1) = -2 by decide))
          (show (1 : ℤ) + (-2) = -1 by decide)) (zero_add (-1))) := by
  rw [moduleConeCompContractingElement, map_neg, moduleHomCompose_π,
    moduleConeCompContractingMiddle, moduleHomCompose_π,
    moduleConeCompContractingLeft, moduleHomCompose_π,
    moduleConeSndElement_π, moduleConeFstElement_π, moduleConeInlElement_π, moduleConeInlElement_π]

lemma moduleConeCompContractingElement_d {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    (moduleHom A D
      (ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeCompMap A D f g)))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeCompMap A D f g)))).d (-1) 0
        (moduleConeCompContractingElement A D f g) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (moduleConeCompInv A D f g ≫ moduleConeCompHom A D f g))).val -
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (𝟙 (moduleCone A D (moduleConeCompMap A D f g))))).val := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomElement_d_π, moduleConeCompContractingElement_π, map_sub,
    ← moduleEvaluation_cochain, ← moduleEvaluation_cochain,
    (moduleEvaluation A D x).map_comp (moduleConeCompInv A D f g) (moduleConeCompHom A D f g),
    moduleConeCompInv_eval, moduleConeCompHom_eval, CategoryTheory.Functor.map_id]
  exact complexConeComp_inv_hom_boundary _ _ _ _ _ _

/-- 逆順の比較射の合成を恒等射へ収縮する全dg自然なホモトピー。 -/
def moduleConeCompInvHomHomotopy {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    ModuleHomotopy A D (moduleConeCompInv A D f g ≫ moduleConeCompHom A D f g) (𝟙 _) :=
  ⟨moduleConeCompContractingElement A D f g, moduleConeCompContractingElement_d A D f g⟩

/-- cone(g)とcone(cone(f)→cone(f≫g))はK(D)で同型。 -/
def moduleConeCompHomotopyIso {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    (moduleToHomotopy A D).obj (moduleCone A D g) ≅
      (moduleToHomotopy A D).obj (moduleCone A D (moduleConeCompMap A D f g)) where
  hom := (moduleToHomotopy A D).map (moduleConeCompHom A D f g)
  inv := (moduleToHomotopy A D).map (moduleConeCompInv A D f g)
  hom_inv_id := by
    rw [← CategoryTheory.Functor.map_comp, moduleConeComp_hom_inv, CategoryTheory.Functor.map_id]
  inv_hom_id := by
    rw [← CategoryTheory.Functor.map_comp]
    exact ((moduleToHomotopy_map_eq_iff A D _ _).2
      ⟨moduleConeCompInvHomHomotopy A D f g⟩).trans ((moduleToHomotopy A D).map_id _)

end SerrePositivity.DifferentialGraded
end

end ConeCompositionHomotopy
