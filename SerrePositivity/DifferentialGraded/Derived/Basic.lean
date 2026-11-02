module

public import SerrePositivity.DifferentialGraded.Module.Disk
public import Mathlib.CategoryTheory.Localization.HasLocalization
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
public import Mathlib.CategoryTheory.Localization.LocalizerMorphism
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction
public import SerrePositivity.DifferentialGraded.Functor.Closed
public import SerrePositivity.DifferentialGraded.Module.Hom.ColimitsAndRightHom
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison
public import Mathlib.CategoryTheory.Localization.Quotient
public import Mathlib.CategoryTheory.Shift.Localization
public import SerrePositivity.DifferentialGraded.Module.MaurerCartanTriangulated
public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Preadditive
public import Mathlib.CategoryTheory.Localization.Linear
public import SerrePositivity.DifferentialGraded.Module.Basic
public import SerrePositivity.DifferentialGraded.Module.TensorFree
public import SerrePositivity.DifferentialGraded.Complexes.TensorShift
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct
public import SerrePositivity.DifferentialGraded.Module.Graded
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import SerrePositivity.DifferentialGraded.Functor.ModuleShift
public import SerrePositivity.HomologicalAlgebra.Complex.ConeLES

/-!
# Derived.Basic

## 概要
26 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## Basic（旧 SerrePositivity/DifferentialGraded/Derived/Basic.lean） -/

/-! # objectwise quasiIso の局所化による導来加群圏

Mathlib の構成された局所化を使用する。対象宇宙は max (u+1) v、
射宇宙も max (u+1) v。この段階ではより小さい射宇宙を主張しない。
閉零圏と K(D) の両方の局所化を定義し、比較は後続の cylinder 証明で行う。
-/

@[expose] public section Basic
universe u v w w'

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全 dg 自然な閉零射の objectwise quasiIso による構成された局所化 D(D)。 -/
abbrev DerivedModuleCategory := (moduleQuasiIso A D).Localization

/-- 閉零加群圏から D(D) への指定局所化関手。 -/
abbrev moduleToDerived : ModuleCategory A D ⥤ DerivedModuleCategory A D :=
  (moduleQuasiIso A D).Q

/-- 比較対象：K(D) を同じ objectwise quasiIso で局所化する。 -/
abbrev HomotopyDerivedModuleCategory := (moduleHomotopyQuasiIso A D).Localization

/-- K(D) からその quasiIso 局所化への指定関手。 -/
abbrev moduleHomotopyToDerived : ModuleHomotopyCategory A D ⥤
    HomotopyDerivedModuleCategory A D := (moduleHomotopyQuasiIso A D).Q

/-- 標準射宇宙における HasLocalization の具体的データ。小さい射宇宙の選択を強制しない。 -/
@[instance_reducible]
def moduleStandardLocalization : (moduleQuasiIso A D).HasLocalization.{max (u + 1) v} :=
  MorphismProperty.HasLocalization.standard _

lemma moduleToDerived_inverts : (moduleQuasiIso A D).IsInvertedBy (moduleToDerived A D) :=
  Localization.inverts _ _

lemma moduleHomotopyToDerived_inverts :
    (moduleHomotopyQuasiIso A D).IsInvertedBy (moduleHomotopyToDerived A D) :=
  Localization.inverts _ _

/-- 指定準同型の像の同型。 -/
def moduleDerivedIso {M N : ModuleCategory A D} (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    (moduleToDerived A D).obj M ≅ (moduleToDerived A D).obj N :=
  Localization.Construction.wIso (W := moduleQuasiIso A D) f hf

variable {E : Type w} [Category.{w'} E]

/-- 指定射を反転する任意の関手の厳密な延長。対象圏の宇宙は独立。 -/
def moduleDerivedLift (F : ModuleCategory A D ⥤ E)
    (hF : (moduleQuasiIso A D).IsInvertedBy F) : DerivedModuleCategory A D ⥤ E :=
  Localization.Construction.lift F hF

lemma moduleDerivedLift_fac (F : ModuleCategory A D ⥤ E)
    (hF : (moduleQuasiIso A D).IsInvertedBy F) :
    moduleToDerived A D ⋙ moduleDerivedLift A D F hF = F :=
  Localization.Construction.fac F hF

lemma moduleDerivedLift_unique (F G : DerivedModuleCategory A D ⥤ E)
    (h : moduleToDerived A D ⋙ F = moduleToDerived A D ⋙ G) : F = G :=
  Localization.Construction.uniq F G h

/-- 自然変換も局所化前の対象上の成分で判定できる。 -/
lemma moduleDerivedNatTrans_ext {F G : DerivedModuleCategory A D ⥤ E} {α β : F ⟶ G}
    (h : ∀ M : ModuleCategory A D,
      α.app ((moduleToDerived A D).obj M) = β.app ((moduleToDerived A D).obj M)) : α = β :=
  Localization.natTrans_ext (moduleToDerived A D) (moduleQuasiIso A D) h

/-- 関手と自然変換を含む局所化の普遍性。 -/
def moduleDerivedUniversalEquivalence (E : Type w) [Category.{w'} E] :
    (DerivedModuleCategory A D ⥤ E) ≌ (moduleQuasiIso A D).FunctorsInverting E :=
  Localization.functorEquivalence (moduleToDerived A D) (moduleQuasiIso A D) E

end SerrePositivity.DifferentialGraded
end

end Basic

/-! ## LeftBasic（旧 SerrePositivity/DifferentialGraded/Derived/LeftBasic.lean） -/

/-! # 左dg加群の指定準同型局所化 -/

@[expose] public section LeftBasic
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 左加群閉零圏のobjectwise quasiIsoによる構成された局所化。 -/
abbrev DerivedLeftModuleCategory := (leftModuleQuasiIso A D).Localization

/-- 左加群の指定局所化関手。 -/
abbrev leftModuleToDerived : LeftModuleCategory A D ⥤ DerivedLeftModuleCategory A D :=
  (leftModuleQuasiIso A D).Q

lemma leftModuleToDerived_inverts :
    (leftModuleQuasiIso A D).IsInvertedBy (leftModuleToDerived A D) :=
  Localization.inverts _ _

/-- 指定された左準同型の像の同型。 -/
def leftModuleDerivedIso {L L' : LeftModuleCategory A D} (g : L ⟶ L')
    (hg : leftModuleQuasiIso A D g) :
    (leftModuleToDerived A D).obj L ≅ (leftModuleToDerived A D).obj L' :=
  Localization.Construction.wIso (W := leftModuleQuasiIso A D) g hg

end SerrePositivity.DifferentialGraded
end

end LeftBasic

/-! ## Evaluation（旧 SerrePositivity/DifferentialGraded/Derived/Evaluation.lean） -/

/-! # 導来加群圏の評価・ホモロジーと局所化による準同型判定

既存 DerivedCategory の射宇宙は HasDerivedCategory.{w} により明示的に選ぶ。
準同型判定を証明するだけの箇所には選択を要求しない。
-/

@[expose] public section Evaluation
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 加群の各対象・整数次数での通常ホモロジー。 -/
def moduleHomology (x : D) (i : ℤ) : ModuleCategory A D ⥤ ModuleCat A :=
  moduleEvaluation A D x ⋙ HomologicalComplex.homologyFunctor (ModuleCat A) (.up ℤ) i

lemma moduleHomology_inverts (x : D) (i : ℤ) :
    (moduleQuasiIso A D).IsInvertedBy (moduleHomology A D x i) := by
  intro M N f hf
  have : QuasiIso ((moduleEvaluation A D x).map f) := hf x
  change IsIso (homologyMap ((moduleEvaluation A D x).map f) i)
  infer_instance

/-- 指定局所化の普遍性による導来加群の評価ホモロジー。 -/
def moduleDerivedHomology (x : D) (i : ℤ) : DerivedModuleCategory A D ⥤ ModuleCat A :=
  moduleDerivedLift A D (moduleHomology A D x i) (moduleHomology_inverts A D x i)

lemma moduleDerivedHomology_fac (x : D) (i : ℤ) :
    moduleToDerived A D ⋙ moduleDerivedHomology A D x i = moduleHomology A D x i :=
  moduleDerivedLift_fac A D _ _

/-- 局所化で同型になる元の射はちょうど指定 objectwise quasiIso。
ホモロジー関手への延長が逆向きを検出する。 -/
lemma moduleToDerived_map_isIso_iff {M N : ModuleCategory A D} (f : M ⟶ N) :
    IsIso ((moduleToDerived A D).map f) ↔ moduleQuasiIso A D f := by
  constructor
  · intro hf x
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    have : IsIso ((moduleToDerived A D).map f) := hf
    have hmap : IsIso ((moduleDerivedHomology A D x i).map ((moduleToDerived A D).map f)) :=
      (moduleDerivedHomology A D x i).map_isIso _
    change IsIso ((moduleToDerived A D ⋙ moduleDerivedHomology A D x i).map f) at hmap
    rw [moduleDerivedHomology_fac] at hmap
    exact hmap
  · intro hf
    exact moduleToDerived_inverts A D f hf

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- 元の加群評価を既存 DerivedCategory の指定局所化へ合成する。 -/
def moduleEvaluationToDerived (x : D) : ModuleCategory A D ⥤ DerivedCategory (ModuleCat A) :=
  moduleEvaluation A D x ⋙ DerivedCategory.Q

lemma moduleEvaluationToDerived_inverts (x : D) :
    (moduleQuasiIso A D).IsInvertedBy (moduleEvaluationToDerived A D x) := by
  intro M N f hf
  have : QuasiIso ((moduleEvaluation A D x).map f) := hf x
  change IsIso (DerivedCategory.Q.map ((moduleEvaluation A D x).map f))
  infer_instance

/-- 導来加群を各対象で既存の A 複体導来圏へ評価する。 -/
def moduleDerivedEvaluation (x : D) : DerivedModuleCategory A D ⥤ DerivedCategory (ModuleCat A) :=
  moduleDerivedLift A D (moduleEvaluationToDerived A D x)
    (moduleEvaluationToDerived_inverts A D x)

lemma moduleDerivedEvaluation_fac (x : D) :
    moduleToDerived A D ⋙ moduleDerivedEvaluation A D x = moduleEvaluationToDerived A D x :=
  moduleDerivedLift_fac A D _ _

end SerrePositivity.DifferentialGraded
end

end Evaluation

/-! ## Shift（旧 SerrePositivity/DifferentialGraded/Derived/Shift.lean） -/

/-! # 指定局所化の整数 shift と導来評価の CommShift -/

@[expose] public section Shift
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

instance moduleEvaluationToDerivedCommShift (x : D) :
    (moduleEvaluationToDerived A D x).CommShift ℤ := by
  unfold moduleEvaluationToDerived
  infer_instance

/-- 厳密な因子化をMathlibの局所化Liftingとして登録する。 -/
instance moduleDerivedEvaluationLifting (x : D) :
    Localization.Lifting (moduleToDerived A D) (moduleQuasiIso A D)
      (moduleEvaluationToDerived A D x) (moduleDerivedEvaluation A D x) :=
  ⟨eqToIso (moduleDerivedEvaluation_fac A D x)⟩

/-- 導来評価は整数shiftと、そのzero/add coherenceを保存する。 -/
instance moduleDerivedEvaluationCommShift (x : D) :
    (moduleDerivedEvaluation A D x).CommShift ℤ :=
  Functor.commShiftOfLocalization (moduleToDerived A D) (moduleQuasiIso A D) ℤ
    (moduleEvaluationToDerived A D x) (moduleDerivedEvaluation A D x)

/-- 導来評価の因子化自然同型もshiftに整合する。 -/
instance moduleDerivedEvaluationFacCommShift (x : D) :
    NatTrans.CommShift (eqToIso (moduleDerivedEvaluation_fac A D x)).hom ℤ := by
  change NatTrans.CommShift
    (Localization.Lifting.iso (moduleToDerived A D) (moduleQuasiIso A D)
      (moduleEvaluationToDerived A D x) (moduleDerivedEvaluation A D x)).hom ℤ
  exact NatTrans.commShift_iso_hom_of_localization (moduleToDerived A D) (moduleQuasiIso A D) ℤ
    (moduleEvaluationToDerived A D x) (moduleDerivedEvaluation A D x)

end SerrePositivity.DifferentialGraded
end

end Shift

/-! ## Ring（旧 SerrePositivity/DifferentialGraded/Derived/Ring.lean） -/

/-! # 一対象 A の導来加群圏と既存 DerivedCategory の自然比較

既存の閉零加群圏同値は指定quasiIsoのクラスを保ち、反映する。
したがって局所化の一般論により、任意の明示的に選ばれた既存導来圏との同値を得る。
-/

@[expose] public section Ring
universe u w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A]

/-- 一対象環の指定準同型判定は既存複体の判定そのもの。 -/
lemma ringModuleQuasiIso_iff {M N : ModuleCategory A PUnit.{1}} (f : M ⟶ N) :
    moduleQuasiIso A PUnit.{1} f ↔
      QuasiIso ((moduleEvaluation A PUnit.{1} PUnit.unit).map f) := by
  constructor
  · exact fun h => h PUnit.unit
  · intro h x
    cases x
    exact h

/-- 一対象の加群圏同値を指定quasiIsoのlocalizerの射として公開する。 -/
def ringModuleLocalizer : LocalizerMorphism (moduleQuasiIso A PUnit.{1})
    (HomologicalComplex.quasiIso (ModuleCat A) (.up ℤ)) where
  functor := moduleEvaluation A PUnit.{1} PUnit.unit
  map _ _ f hf := (ringModuleQuasiIso_iff A f).1 hf

instance ringModuleLocalizerIsInduced : (ringModuleLocalizer A).IsInduced where
  inverseImage_eq := by
    ext M N f
    exact (ringModuleQuasiIso_iff A f).symm

instance ringModuleLocalizerFunctorIsEquivalence : (ringModuleLocalizer A).functor.IsEquivalence :=
  ringEvaluation_isEquivalence A

instance ringModuleLocalizerIsLocalizedEquivalence :
    (ringModuleLocalizer A).IsLocalizedEquivalence :=
  (ringModuleLocalizer A).isLocalizedEquivalence_of_isInduced

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- U9で構成した導来評価自体が、一対象環では圏同値となる。 -/
instance ringDerivedEvaluationIsEquivalence :
    (moduleDerivedEvaluation A PUnit.{1} PUnit.unit).IsEquivalence := by
  let : CatCommSq (ringModuleLocalizer A).functor (moduleToDerived A PUnit.{1})
      (DerivedCategory.Q (C := ModuleCat A)) (moduleDerivedEvaluation A PUnit.{1} PUnit.unit) :=
    CatCommSq.mk (eqToIso (moduleDerivedEvaluation_fac A PUnit.{1} PUnit.unit).symm)
  exact (ringModuleLocalizer A).isEquivalence (moduleToDerived A PUnit.{1}) DerivedCategory.Q _

/-- 一対象 A の主導来加群圏と既存の A 複体導来圏の同値。 -/
def ringDerivedEquivalence : DerivedModuleCategory A PUnit.{1} ≌ DerivedCategory (ModuleCat A) :=
  (moduleDerivedEvaluation A PUnit.{1} PUnit.unit).asEquivalence

/-- 主局所化と既存複体の局所化を結ぶ比較自然同型。 -/
def ringDerivedEquivalence_fac :
    moduleToDerived A PUnit.{1} ⋙ (ringDerivedEquivalence A).functor ≅
      (ringModuleEquivalence A).functor ⋙ DerivedCategory.Q :=
  eqToIso (moduleDerivedEvaluation_fac A PUnit.{1} PUnit.unit)

/-- 一対象比較は導来圏の整数shiftとzero/add coherenceを保存する。 -/
instance ringModuleEquivalenceCommShift : (ringModuleEquivalence A).functor.CommShift ℤ :=
  moduleEvaluationCommShift A PUnit.{1} PUnit.unit

/-- 導来圏の一対象比較の整合的shift。 -/
instance ringDerivedEquivalenceCommShift : (ringDerivedEquivalence A).functor.CommShift ℤ :=
  moduleDerivedEvaluationCommShift A PUnit.{1} PUnit.unit

/-- 局所化比較の自然同型も整数shiftに整合する。 -/
instance ringDerivedEquivalenceFacCommShift :
    NatTrans.CommShift (ringDerivedEquivalence_fac A).hom ℤ := by
  change NatTrans.CommShift
    (eqToIso (moduleDerivedEvaluation_fac A PUnit.{1} PUnit.unit)).hom ℤ
  exact moduleDerivedEvaluationFacCommShift A PUnit.{1} PUnit.unit

end SerrePositivity.DifferentialGraded
end

end Ring

/-! ## Restriction（旧 SerrePositivity/DifferentialGraded/Derived/Restriction.lean） -/

/-! # dg関手に沿う右dg加群の導来制限

## 概要
制限は対象ごとに評価するため任意の準同型を保ち、置換を要さず主局所化へ降りる。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section Restriction
universe u v w

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

/-- opposite上の指定dg関手に沿う導来制限。 -/
def moduleDerivedRestriction (F : DGFunctor A Dᵒᵖ Eᵒᵖ) :
    DerivedModuleCategory A E ⥤ DerivedModuleCategory A D :=
  moduleDerivedLift A E (moduleRestriction A D E F ⋙ moduleToDerived A D) (by
    intro M N f hf
    exact moduleToDerived_inverts A D _ (moduleRestriction_quasiIso A D E F f hf))

lemma moduleDerivedRestriction_fac (F : DGFunctor A Dᵒᵖ Eᵒᵖ) :
    moduleToDerived A E ⋙ moduleDerivedRestriction A D E F =
      moduleRestriction A D E F ⋙ moduleToDerived A D := moduleDerivedLift_fac _ _ _ _

/-- 通常向きのdg関手からoppositeを構成して制限する入口。 -/
def dgDerivedRestriction (F : DGFunctor A D E) :
    DerivedModuleCategory A E ⥤ DerivedModuleCategory A D :=
  moduleDerivedRestriction A D E F.op

lemma dgDerivedRestriction_fac (F : DGFunctor A D E) :
    moduleToDerived A E ⋙ dgDerivedRestriction A D E F =
      moduleRestriction A D E F.op ⋙ moduleToDerived A D :=
  moduleDerivedRestriction_fac A D E F.op

end SerrePositivity.DifferentialGraded
end

end Restriction

/-! ## RestrictionCoherence（旧 SerrePositivity/DifferentialGraded/Derived/RestrictionCoherence.lean） -/

/-! # 導来制限の恒等・合成比較と局所化前での計算

## 概要
導来制限の恒等・合成比較と局所化前での計算。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section RestrictionCoherence
universe u v w z

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance moduleDerivedRestriction_lifting (E : Type w) [DGCategory A E] [Small.{u} E]
    (F : DGFunctor A Dᵒᵖ Eᵒᵖ) :
    Localization.Lifting (moduleToDerived A E) (moduleQuasiIso A E)
      (moduleRestriction A D E F ⋙ moduleToDerived A D) (moduleDerivedRestriction A D E F) :=
  ⟨eqToIso (moduleDerivedRestriction_fac A D E F)⟩

def moduleDerivedRestrictionIdIso :
    moduleDerivedRestriction A D D (DGFunctor.id Dᵒᵖ) ≅ 𝟭 (DerivedModuleCategory A D) :=
  Localization.liftNatIso (moduleToDerived A D) (moduleQuasiIso A D)
    (moduleRestriction A D D (DGFunctor.id Dᵒᵖ) ⋙ moduleToDerived A D) (moduleToDerived A D)
    (moduleDerivedRestriction A D D (DGFunctor.id Dᵒᵖ)) (𝟭 _)
    (Functor.isoWhiskerRight (moduleRestrictionIdIso A D) (moduleToDerived A D))

variable (E : Type w) [DGCategory A E] [Small.{u} E]
  (T : Type z) [DGCategory A T] [Small.{u} T]
  (F : DGFunctor A Dᵒᵖ Eᵒᵖ) (G : DGFunctor A Eᵒᵖ Tᵒᵖ)

lemma moduleDerivedRestrictionComp_fac :
    moduleToDerived A T ⋙ (moduleDerivedRestriction A E T G ⋙ moduleDerivedRestriction A D E F) =
      (moduleRestriction A E T G ⋙ moduleRestriction A D E F) ⋙ moduleToDerived A D := by
  rw [← Functor.assoc, moduleDerivedRestriction_fac, Functor.assoc,
    moduleDerivedRestriction_fac, ← Functor.assoc]

instance moduleDerivedRestrictionComp_lifting :
    Localization.Lifting (moduleToDerived A T) (moduleQuasiIso A T)
      ((moduleRestriction A E T G ⋙ moduleRestriction A D E F) ⋙ moduleToDerived A D)
      (moduleDerivedRestriction A E T G ⋙ moduleDerivedRestriction A D E F) :=
  ⟨eqToIso (moduleDerivedRestrictionComp_fac A D E T F G)⟩

def moduleDerivedRestrictionCompIso :
    moduleDerivedRestriction A E T G ⋙ moduleDerivedRestriction A D E F ≅
      moduleDerivedRestriction A D T (F.comp G) :=
  Localization.liftNatIso (moduleToDerived A T) (moduleQuasiIso A T)
    ((moduleRestriction A E T G ⋙ moduleRestriction A D E F) ⋙ moduleToDerived A D)
    (moduleRestriction A D T (F.comp G) ⋙ moduleToDerived A D)
    (moduleDerivedRestriction A E T G ⋙ moduleDerivedRestriction A D E F)
    (moduleDerivedRestriction A D T (F.comp G))
    (Functor.isoWhiskerRight (moduleRestrictionCompIso A D E T F G) (moduleToDerived A D))

lemma moduleDerivedRestrictionCompIso_hom_app (M : ModuleCategory A T) :
    (moduleDerivedRestrictionCompIso A D E T F G).hom.app ((moduleToDerived A T).obj M) =
      (Localization.Lifting.iso (moduleToDerived A T) (moduleQuasiIso A T)
        ((moduleRestriction A E T G ⋙ moduleRestriction A D E F) ⋙ moduleToDerived A D)
        (moduleDerivedRestriction A E T G ⋙ moduleDerivedRestriction A D E F)).hom.app M ≫
      (moduleToDerived A D).map (moduleRestrictionCompObjIso A D E T F G M).hom ≫
      (Localization.Lifting.iso (moduleToDerived A T) (moduleQuasiIso A T)
        (moduleRestriction A D T (F.comp G) ⋙ moduleToDerived A D)
        (moduleDerivedRestriction A D T (F.comp G))).inv.app M :=
  Localization.liftNatTrans_app _ _ _ _ _ _ _ _

end SerrePositivity.DifferentialGraded
end

end RestrictionCoherence

/-! ## HomotopyComparison（旧 SerrePositivity/DifferentialGraded/Derived/HomotopyComparison.lean） -/

/-! # 閉零加群圏と K(D) の指定局所化の比較

具体的 dg cylinder が境界を同一視させることを証明し、
Mathlib の商の局所化と局所化の一意性を適用する。
-/

@[expose] public section HomotopyComparison
universe u v w w'

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 指定quasiIsoを反転する任意の関手は加群の境界関係を同一視する。 -/
lemma moduleQuasiIso_equalizes_boundary {E : Type w} [Category.{w'} E]
    (F : ModuleCategory A D ⥤ E) (hF : (moduleQuasiIso A D).IsInvertedBy F)
    {M N : ModuleCategory A D} (f g : M ⟶ N)
    (h : boundaryRelation A (RightModule A D) f g) : F.map f = F.map g := by
  let P := modulePrecylinder A D M
  let H := moduleCylinderLeftHomotopy A D f g h
  let e : F.obj P.I ≅ F.obj M := @asIso E _ _ _ (F.map P.π)
    (hF _ (modulePrecylinder_π_quasiIso A D M))
  have hi : F.map P.i₀ = F.map P.i₁ := by
    have hs : F.map P.i₀ ≫ e.hom = F.map P.i₁ ≫ e.hom := by
      change F.map P.i₀ ≫ F.map P.π = F.map P.i₁ ≫ F.map P.π
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, P.i₀_π, P.i₁_π]
    have hc := congrArg (fun k => k ≫ e.inv) hs
    simpa only [Category.assoc, e.hom_inv_id, Category.comp_id] using hc
  calc
    F.map f = F.map (P.i₀ ≫ H.h) := congrArg F.map H.h₀.symm
    _ = F.map P.i₀ ≫ F.map H.h := F.map_comp _ _
    _ = F.map P.i₁ ≫ F.map H.h := congrArg (fun k => k ≫ F.map H.h) hi
    _ = F.map g := (F.map_comp _ _).symm.trans (congrArg F.map H.h₁)

lemma moduleBoundaryFactorsThroughLocalization :
    (boundaryRelation A (RightModule A D)).FactorsThroughLocalization (moduleQuasiIso A D) := by
  intro M N f g h
  exact moduleQuasiIso_equalizes_boundary A D (moduleToDerived A D)
    (moduleToDerived_inverts A D) f g h

/-- K(D)を経由した局所化も閉零圏の同じquasiIsoを局所化する。 -/
instance moduleHomotopyCompositeIsLocalization :
    (moduleToHomotopy A D ⋙ moduleHomotopyToDerived A D).IsLocalization (moduleQuasiIso A D) := by
  apply Functor.IsLocalization.mk'
  all_goals
    exact ((moduleBoundaryFactorsThroughLocalization A D).strictUniversalPropertyFixedTarget'
      (W' := moduleHomotopyQuasiIso A D) (moduleHomotopyQuasiIso_inverseImage A D).symm _)

/-- 指定した二つの局所化の同値。 -/
def moduleDerivedHomotopyEquivalence :
    DerivedModuleCategory A D ≌ HomotopyDerivedModuleCategory A D :=
  Localization.uniq (moduleToDerived A D)
    (moduleToHomotopy A D ⋙ moduleHomotopyToDerived A D) (moduleQuasiIso A D)

/-- 同値の順方向と二つの局所化関手の可換図式。 -/
def moduleDerivedHomotopyComparisonIso :
    moduleToDerived A D ⋙ (moduleDerivedHomotopyEquivalence A D).functor ≅
      moduleToHomotopy A D ⋙ moduleHomotopyToDerived A D :=
  Localization.compUniqFunctor (moduleToDerived A D)
    (moduleToHomotopy A D ⋙ moduleHomotopyToDerived A D) (moduleQuasiIso A D)

/-- 逆方向についても局所化関手の比較を公開する。 -/
def moduleDerivedHomotopyInverseComparisonIso :
    (moduleToHomotopy A D ⋙ moduleHomotopyToDerived A D) ⋙
      (moduleDerivedHomotopyEquivalence A D).inverse ≅ moduleToDerived A D :=
  Localization.compUniqInverse (moduleToDerived A D)
    (moduleToHomotopy A D ⋙ moduleHomotopyToDerived A D) (moduleQuasiIso A D)

/-- 主導来加群圏への K(D) の局所化関手。 -/
def moduleHomotopyToDerivedClosed : ModuleHomotopyCategory A D ⥤ DerivedModuleCategory A D :=
  moduleHomotopyToDerived A D ⋙ (moduleDerivedHomotopyEquivalence A D).inverse

instance moduleHomotopyToDerivedClosedIsLocalization :
    (moduleHomotopyToDerivedClosed A D).IsLocalization (moduleHomotopyQuasiIso A D) := by
  unfold moduleHomotopyToDerivedClosed
  infer_instance

/-- 閉零→K(D)→D(D) と主局所化の比較自然同型。 -/
def moduleToHomotopyDerivedIso :
    moduleToHomotopy A D ⋙ moduleHomotopyToDerivedClosed A D ≅ moduleToDerived A D :=
  (Functor.associator _ _ _).symm ≪≫ moduleDerivedHomotopyInverseComparisonIso A D

end SerrePositivity.DifferentialGraded
end

end HomotopyComparison

/-! ## HomotopyShift（旧 SerrePositivity/DifferentialGraded/Derived/HomotopyShift.lean） -/

/-! # K(D)から主導来圏への局所化関手の整合的shift -/

@[expose] public section HomotopyShift
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance moduleHomotopyDerivedInverseLifting :
    Localization.Lifting (moduleToHomotopy A D ⋙ moduleHomotopyToDerived A D)
      (moduleQuasiIso A D) (moduleToDerived A D) (moduleDerivedHomotopyEquivalence A D).inverse :=
  ⟨moduleDerivedHomotopyInverseComparisonIso A D⟩

instance moduleHomotopyDerivedInverseCommShift :
    (moduleDerivedHomotopyEquivalence A D).inverse.CommShift ℤ :=
  Functor.commShiftOfLocalization (moduleToHomotopy A D ⋙ moduleHomotopyToDerived A D)
    (moduleQuasiIso A D) ℤ (moduleToDerived A D) (moduleDerivedHomotopyEquivalence A D).inverse

instance moduleHomotopyDerivedInverseComparisonCommShift :
    NatTrans.CommShift (moduleDerivedHomotopyInverseComparisonIso A D).hom ℤ := by
  change NatTrans.CommShift
    (Localization.Lifting.iso (moduleToHomotopy A D ⋙ moduleHomotopyToDerived A D)
      (moduleQuasiIso A D) (moduleToDerived A D)
      (moduleDerivedHomotopyEquivalence A D).inverse).hom ℤ
  exact NatTrans.commShift_iso_hom_of_localization
    (moduleToHomotopy A D ⋙ moduleHomotopyToDerived A D) (moduleQuasiIso A D) ℤ
    (moduleToDerived A D) (moduleDerivedHomotopyEquivalence A D).inverse

instance moduleHomotopyToDerivedClosedCommShift :
    (moduleHomotopyToDerivedClosed A D).CommShift ℤ := by
  unfold moduleHomotopyToDerivedClosed
  infer_instance

instance moduleToHomotopyDerivedIsoCommShift :
    NatTrans.CommShift (moduleToHomotopyDerivedIso A D).hom ℤ := by
  change NatTrans.CommShift
    ((Functor.associator (moduleToHomotopy A D) (moduleHomotopyToDerived A D)
      (moduleDerivedHomotopyEquivalence A D).inverse).inv ≫
        (moduleDerivedHomotopyInverseComparisonIso A D).hom) ℤ
  apply NatTrans.CommShift.comp

end SerrePositivity.DifferentialGraded
end

end HomotopyShift

/-! ## Triangulated（旧 SerrePositivity/DifferentialGraded/Derived/Triangulated.lean） -/

/-! # 指定された導来加群圏の三角構造とVerdier局所化 -/

@[expose] public section Triangulated
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance moduleHomotopyQuasiIsoLeftFractions :
    (moduleHomotopyQuasiIso A D).HasLeftCalculusOfFractions := by
  rw [← moduleHomotopyAcyclic_trW_eq A D]
  infer_instance

instance moduleHomotopyQuasiIsoRightFractions :
    (moduleHomotopyQuasiIso A D).HasRightCalculusOfFractions := by
  rw [← moduleHomotopyAcyclic_trW_eq A D]
  infer_instance

instance moduleHomotopyQuasiIsoTriangulation :
    (moduleHomotopyQuasiIso A D).IsCompatibleWithTriangulation := by
  rw [← moduleHomotopyAcyclic_trW_eq A D]
  infer_instance

instance moduleDerivedPreadditive : Preadditive (DerivedModuleCategory A D) :=
  Localization.preadditive (moduleHomotopyToDerivedClosed A D) (moduleHomotopyQuasiIso A D)

instance moduleHomotopyToDerivedClosedAdditive : (moduleHomotopyToDerivedClosed A D).Additive :=
  Localization.functor_additive (moduleHomotopyToDerivedClosed A D) (moduleHomotopyQuasiIso A D)

instance moduleDerivedHasZeroObject : HasZeroObject (DerivedModuleCategory A D) :=
  (moduleHomotopyToDerivedClosed A D).hasZeroObject_of_additive

instance moduleDerivedShiftAdditive (s : ℤ) :
    (shiftFunctor (DerivedModuleCategory A D) s).Additive := by
  rw [Localization.functor_additive_iff
    (moduleHomotopyToDerivedClosed A D) (moduleHomotopyQuasiIso A D)]
  exact Functor.additive_of_iso ((moduleHomotopyToDerivedClosed A D).commShiftIso s)

/-- U9で構成した主導来圏そのものにVerdier局所化の三角構造を入れる。 -/
instance moduleDerivedPretriangulated : Pretriangulated (DerivedModuleCategory A D) :=
  Triangulated.Localization.pretriangulated
    (moduleHomotopyToDerivedClosed A D) (moduleHomotopyQuasiIso A D)

instance moduleHomotopyToDerivedClosedIsTriangulated :
    (moduleHomotopyToDerivedClosed A D).IsTriangulated :=
  Triangulated.Localization.isTriangulated_functor
    (moduleHomotopyToDerivedClosed A D) (moduleHomotopyQuasiIso A D)

instance moduleDerivedIsTriangulated : IsTriangulated (DerivedModuleCategory A D) :=
  Triangulated.Localization.isTriangulated
    (moduleHomotopyToDerivedClosed A D) (moduleHomotopyQuasiIso A D)

instance moduleHomotopyToDerivedClosedArrowEssSurj :
    (moduleHomotopyToDerivedClosed A D).mapArrow.EssSurj :=
  Localization.essSurj_mapArrow (moduleHomotopyToDerivedClosed A D) (moduleHomotopyQuasiIso A D)

/-- 主導来圏は、acyclic部分圏のVerdier射を局所化している。 -/
instance moduleHomotopyToDerivedVerdierIsLocalization :
    (moduleHomotopyToDerivedClosed A D).IsLocalization (moduleHomotopyAcyclic A D).trW := by
  rw [moduleHomotopyAcyclic_trW_eq A D]
  infer_instance

lemma moduleDerived_distinguished_iff (T : Triangle (DerivedModuleCategory A D)) :
    T ∈ distTriang (DerivedModuleCategory A D) ↔
      T ∈ (moduleHomotopyToDerivedClosed A D).essImageDistTriang := Iff.rfl

instance moduleHomotopyToDerivedIsTriangulated :
    (moduleHomotopyToDerived A D).IsTriangulated :=
  Triangulated.Localization.isTriangulated_functor
    (moduleHomotopyToDerived A D) (moduleHomotopyQuasiIso A D)

instance moduleHomotopyToDerivedArrowEssSurj :
    (moduleHomotopyToDerived A D).mapArrow.EssSurj :=
  Localization.essSurj_mapArrow (moduleHomotopyToDerived A D) (moduleHomotopyQuasiIso A D)

instance moduleDerivedHomotopyInverseIsTriangulated :
    (moduleDerivedHomotopyEquivalence A D).inverse.IsTriangulated := by
  let : (moduleHomotopyToDerived A D ⋙
      (moduleDerivedHomotopyEquivalence A D).inverse).IsTriangulated :=
    moduleHomotopyToDerivedClosedIsTriangulated A D
  exact Functor.isTriangulated_of_precomp (moduleHomotopyToDerived A D)
    (moduleDerivedHomotopyEquivalence A D).inverse

end SerrePositivity.DifferentialGraded
end

end Triangulated

/-! ## Linear（旧 SerrePositivity/DifferentialGraded/Derived/Linear.lean） -/

/-! # 指定導来局所化の加法性と標準A線形構造への接続 -/

@[expose] public section Linear
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 既存のK(D)経由の因子化から主局所化の加法性を得る。
これによりMathlibの局所化の標準Linear構造と関手の線形性が適用できる。 -/
instance moduleToDerivedAdditive : (moduleToDerived A D).Additive :=
  Functor.additive_of_iso (moduleToHomotopyDerivedIso A D)

end SerrePositivity.DifferentialGraded
end

end Linear

/-! ## AcyclicZero（旧 SerrePositivity/DifferentialGraded/Derived/AcyclicZero.lean） -/

/-! # 主導来圏での零性と評価ホモロジーの消滅 -/

@[expose] public section AcyclicZero
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleAcyclic_zeroTo_quasiIso {N : ModuleCategory A D} (hN : moduleAcyclic A D N) :
    moduleQuasiIso A D (moduleZeroTo A D N) := by
  intro x
  rw [quasiIso_iff]
  intro n
  apply (quasiIsoAt_iff_exactAt _ n ?_).2
  · exact hN x n
  · have hz := (moduleEvaluation A D x).map_isZero (moduleZero_isZero A D)
    exact ExactAt.of_isZero ((HomologicalComplex.eval (ModuleCat A) (.up ℤ) n).map_isZero hz)

lemma moduleToDerived_isZero_of_acyclic {N : ModuleCategory A D} (hN : moduleAcyclic A D N) :
    IsZero ((moduleToDerived A D).obj N) :=
  ((moduleToDerived A D).map_isZero (moduleZero_isZero A D)).of_iso
    (moduleDerivedIso A D (moduleZeroTo A D N) (moduleAcyclic_zeroTo_quasiIso A D hN)).symm

lemma moduleDerived_isZero_iff_homology (X : DerivedModuleCategory A D) :
    IsZero X ↔ ∀ (x : D) (n : ℤ), IsZero ((moduleDerivedHomology A D x n).obj X) := by
  constructor
  · intro hX x n
    have hz : IsZero ((moduleDerivedHomology A D x n).obj
        ((moduleToDerived A D).obj (moduleZero A D))) :=
      (HomologicalComplex.homologyFunctor (ModuleCat A) (.up ℤ) n).map_isZero
        ((moduleEvaluation A D x).map_isZero (moduleZero_isZero A D))
    exact hz.of_iso ((moduleDerivedHomology A D x n).mapIso
      (hX.iso ((moduleToDerived A D).map_isZero (moduleZero_isZero A D))))
  · intro hX
    obtain ⟨⟨N⟩⟩ := X
    apply moduleToDerived_isZero_of_acyclic A D
    intro x n
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2 (hX x n)

lemma moduleToDerived_isZero_iff_acyclic (N : ModuleCategory A D) :
    IsZero ((moduleToDerived A D).obj N) ↔ moduleAcyclic A D N := by
  constructor
  · intro hN x n
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
      ((moduleDerived_isZero_iff_homology A D _).mp hN x n)
  · exact moduleToDerived_isZero_of_acyclic A D

end SerrePositivity.DifferentialGraded
end

end AcyclicZero

/-! ## ConeTriangles（旧 SerrePositivity/DifferentialGraded/Derived/ConeTriangles.lean） -/

/-! # 指定導来圏における実際の加群cone三角形 -/

@[expose] public section ConeTriangles
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleDerivedConeTriangle {M N : ModuleCategory A D} (f : M ⟶ N) :
    Triangle (DerivedModuleCategory A D) :=
  (moduleToDerived A D).mapTriangle.obj (moduleConeTriangle A D f)

/-- 閉零→K(D)→D(D)の比較により、同じ加群coneの像はdistinguished。 -/
lemma moduleDerivedConeTriangle_distinguished {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleDerivedConeTriangle A D f ∈ distTriang (DerivedModuleCategory A D) := by
  let e := (Functor.mapTriangleCompIso (moduleToHomotopy A D)
      (moduleHomotopyToDerivedClosed A D)).symm.app (moduleConeTriangle A D f) ≪≫
    (Functor.mapTriangleIso (moduleToHomotopyDerivedIso A D)).app (moduleConeTriangle A D f)
  exact isomorphic_distinguished _
    ((moduleHomotopyToDerivedClosed A D).map_distinguished _
      (moduleHomotopyConeTriangle_distinguished A D f)) _ e.symm

end SerrePositivity.DifferentialGraded
end

end ConeTriangles

/-! ## HomotopyLinear（旧 SerrePositivity/DifferentialGraded/Derived/HomotopyLinear.lean） -/

/-! # K(D)から主導来圏への比較のA線形性 -/

@[expose] public section HomotopyLinear
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- K(D)から主導来圏への関手はA線形。Qとの比較と商関手の充満・本質的全射性から降下する。 -/
instance moduleHomotopyToDerivedClosedLinear : (moduleHomotopyToDerivedClosed A D).Linear A := by
  have : (moduleToHomotopy A D ⋙ moduleHomotopyToDerivedClosed A D).Linear A :=
    Functor.linear_of_iso A (moduleToHomotopyDerivedIso A D).symm
  exact Functor.linear_of_full_essSurj_comp (moduleToHomotopy A D) _

end SerrePositivity.DifferentialGraded
end

end HomotopyLinear

/-! ## VerdierComparison（旧 SerrePositivity/DifferentialGraded/Derived/VerdierComparison.lean） -/

/-! # 主導来加群圏とacyclic部分圏による標準Verdier商の三角同値 -/

@[expose] public section VerdierComparison
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 指定準同型の主局所化と、acyclic部分圏の標準Verdier局所化との同値。 -/
def moduleDerivedVerdierEquivalence :
    DerivedModuleCategory A D ≌ (moduleHomotopyAcyclic A D).trW.Localization :=
  Localization.uniq (moduleHomotopyToDerivedClosed A D)
    (moduleHomotopyAcyclic A D).trW.Q (moduleHomotopyAcyclic A D).trW

def moduleDerivedVerdierComparisonIso :
    moduleHomotopyToDerivedClosed A D ⋙ (moduleDerivedVerdierEquivalence A D).functor ≅
      (moduleHomotopyAcyclic A D).trW.Q :=
  Localization.compUniqFunctor (moduleHomotopyToDerivedClosed A D)
    (moduleHomotopyAcyclic A D).trW.Q (moduleHomotopyAcyclic A D).trW

instance moduleDerivedVerdierLifting :
    Localization.Lifting (moduleHomotopyToDerivedClosed A D) (moduleHomotopyQuasiIso A D)
      (moduleHomotopyAcyclic A D).trW.Q (moduleDerivedVerdierEquivalence A D).functor :=
  ⟨moduleDerivedVerdierComparisonIso A D⟩

instance moduleDerivedVerdierCommShift :
    (moduleDerivedVerdierEquivalence A D).functor.CommShift ℤ :=
  Functor.commShiftOfLocalization (moduleHomotopyToDerivedClosed A D) (moduleHomotopyQuasiIso A D) ℤ
    (moduleHomotopyAcyclic A D).trW.Q (moduleDerivedVerdierEquivalence A D).functor

instance moduleDerivedVerdierComparisonCommShift :
    NatTrans.CommShift (moduleDerivedVerdierComparisonIso A D).hom ℤ := by
  change NatTrans.CommShift
    (Localization.Lifting.iso (moduleHomotopyToDerivedClosed A D) (moduleHomotopyQuasiIso A D)
      (moduleHomotopyAcyclic A D).trW.Q (moduleDerivedVerdierEquivalence A D).functor).hom ℤ
  exact NatTrans.commShift_iso_hom_of_localization
    (moduleHomotopyToDerivedClosed A D) (moduleHomotopyQuasiIso A D) ℤ
    (moduleHomotopyAcyclic A D).trW.Q (moduleDerivedVerdierEquivalence A D).functor

instance moduleDerivedVerdierIsTriangulated :
    (moduleDerivedVerdierEquivalence A D).functor.IsTriangulated :=
  Functor.isTriangulated_of_precomp_iso
    (F := moduleHomotopyToDerivedClosed A D) (G := (moduleDerivedVerdierEquivalence A D).functor)
    (moduleDerivedVerdierComparisonIso A D)

instance moduleDerivedVerdierInverseCommShift :
    (moduleDerivedVerdierEquivalence A D).inverse.CommShift ℤ :=
  Functor.CommShift.ofComp (moduleDerivedVerdierEquivalence A D).counitIso ℤ

instance moduleDerivedVerdierCounitCommShift :
    NatTrans.CommShift (moduleDerivedVerdierEquivalence A D).counitIso.hom ℤ :=
  Functor.CommShift.ofComp_compatibility (moduleDerivedVerdierEquivalence A D).counitIso ℤ

instance moduleDerivedVerdierInverseIsTriangulated :
    (moduleDerivedVerdierEquivalence A D).inverse.IsTriangulated :=
  (Functor.isTriangulated_iff_comp_right (moduleDerivedVerdierEquivalence A D).counitIso).2
    inferInstance

end SerrePositivity.DifferentialGraded
end

end VerdierComparison

/-! ## EvaluationTriangles（旧 SerrePositivity/DifferentialGraded/Derived/EvaluationTriangles.lean） -/

/-! # 導来評価と一対象A比較の三角性 -/

@[expose] public section EvaluationTriangles
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated

/-- 三段の関手合成の可換squareから、三角形の比較を得る。 -/
def mapTriangleTripleSquareIso {C K E J H : Type*}
    [Category* C] [Category* K] [Category* E] [Category* J] [Category* H]
    [HasShift C ℤ] [HasShift K ℤ] [HasShift E ℤ] [HasShift J ℤ] [HasShift H ℤ]
    (Q : C ⥤ K) (L : K ⥤ E) (G : E ⥤ H) (F : C ⥤ J) (q : J ⥤ H)
    [Q.CommShift ℤ] [L.CommShift ℤ] [G.CommShift ℤ] [F.CommShift ℤ] [q.CommShift ℤ]
    (α : (Q ⋙ L) ⋙ G ≅ F ⋙ q) [NatTrans.CommShift α.hom ℤ]
    (T : Triangle C) (T' : Triangle J) (e : F.mapTriangle.obj T ≅ T') :
    G.mapTriangle.obj (L.mapTriangle.obj (Q.mapTriangle.obj T)) ≅ q.mapTriangle.obj T' :=
  G.mapTriangle.mapIso ((Functor.mapTriangleCompIso Q L).symm.app T) ≪≫
    mapTriangleSquareIso (Q ⋙ L) G F q α T T' e

section General
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- 元の閉零圏から見た導来評価の比較。既存のshift構造を使用する。 -/
def moduleDerivedEvaluationHomotopyFacIso (x : D) :=
  Functor.isoWhiskerRight (moduleToHomotopyDerivedIso A D) (moduleDerivedEvaluation A D x) ≪≫
    eqToIso (moduleDerivedEvaluation_fac A D x)

instance moduleDerivedEvaluationHomotopyFacCommShift (x : D) :
    NatTrans.CommShift (moduleDerivedEvaluationHomotopyFacIso A D x).hom ℤ := by
  change NatTrans.CommShift
    (Functor.whiskerRight (moduleToHomotopyDerivedIso A D).hom (moduleDerivedEvaluation A D x) ≫
      (eqToIso (moduleDerivedEvaluation_fac A D x)).hom) ℤ
  apply NatTrans.CommShift.comp

/-- 導来評価は標準加群cone三角形を既存導来圏の標準cone三角形へ移す。 -/
def moduleDerivedConeTriangleEvaluationIso {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :=
  mapTriangleTripleSquareIso (moduleToHomotopy A D) (moduleHomotopyToDerivedClosed A D)
    (moduleDerivedEvaluation A D x) (moduleEvaluation A D x) (DerivedCategory.Q (C := ModuleCat A))
    (moduleDerivedEvaluationHomotopyFacIso A D x) (moduleConeTriangle A D f)
    (CochainComplex.mappingCone.triangle ((moduleEvaluation A D x).map f))
    (moduleConeTriangleEvaluationIso A D f x)

instance moduleDerivedEvaluationIsTriangulated (x : D) :
    (moduleDerivedEvaluation A D x).IsTriangulated where
  map_distinguished T hT := by
    change ∃ (T₀ : Triangle (ModuleHomotopyCategory A D))
      (_ : T ≅ (moduleHomotopyToDerivedClosed A D).mapTriangle.obj T₀),
        T₀ ∈ distTriang (ModuleHomotopyCategory A D) at hT
    obtain ⟨T₀, e₀, h₀⟩ := hT
    change ∃ (M N : ModuleCategory A D) (f : M ⟶ N), Nonempty
      (T₀ ≅ (moduleToHomotopy A D).mapTriangle.obj (moduleConeTriangle A D f)) at h₀
    obtain ⟨M, N, f, ⟨e₁⟩⟩ := h₀
    exact isomorphic_distinguished _
      (DerivedCategory.mappingCone_triangle_distinguished ((moduleEvaluation A D x).map f)) _
      ((moduleDerivedEvaluation A D x).mapTriangle.mapIso e₀ ≪≫
        (moduleDerivedEvaluation A D x).mapTriangle.mapIso
          ((moduleHomotopyToDerivedClosed A D).mapTriangle.mapIso e₁) ≪≫
        moduleDerivedConeTriangleEvaluationIso A D f x)
end General

section OneObject
variable (A : Type u) [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- 一対象Aの既存導来圏との比較同値はdistinguished三角形を保存する。 -/
instance ringDerivedEquivalenceIsTriangulated : (ringDerivedEquivalence A).functor.IsTriangulated :=
  moduleDerivedEvaluationIsTriangulated A PUnit.{1} PUnit.unit

instance ringDerivedEquivalenceInverseCommShift : (ringDerivedEquivalence A).inverse.CommShift ℤ :=
  Functor.CommShift.ofComp (ringDerivedEquivalence A).counitIso ℤ

instance ringDerivedEquivalenceCounitCommShift :
    NatTrans.CommShift (ringDerivedEquivalence A).counitIso.hom ℤ :=
  Functor.CommShift.ofComp_compatibility (ringDerivedEquivalence A).counitIso ℤ

instance ringDerivedEquivalenceInverseIsTriangulated :
    (ringDerivedEquivalence A).inverse.IsTriangulated :=
  (Functor.isTriangulated_iff_comp_right (ringDerivedEquivalence A).counitIso).2 inferInstance
end OneObject

end SerrePositivity.DifferentialGraded
end

end EvaluationTriangles

/-! ## HomotopicallyProjective（旧 SerrePositivity/DifferentialGraded/Derived/HomotopicallyProjective.lean） -/

/-! # dg 加群の homotopically projective 性

全次数 Hom end が objectwise acyclic 加群を acyclic 複体へ送る性質。
各評価複体の K-projective 性で代用せず、Mathlib の複体 IsKProjective とは区別する。
-/

@[expose] public section HomotopicallyProjective
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全次数の Hom end が acyclic 加群を消すという dg 加群の性質。 -/
def moduleHomotopicallyProjective : ObjectProperty (ModuleCategory A D) :=
  fun M => ∀ N : ModuleCategory A D, moduleAcyclic A D N →
    (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N)).Acyclic

/-- dg Yoneda により右代表加群は任意の小さい dg 圏上で homotopically projective。
Hom_D の A 上のprojectivityやflatnessは不要。 -/
lemma representable_homotopicallyProjective (x : D) :
    moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) (representable A x)) := by
  intro N hN i
  exact (hN x i).of_iso (dgYonedaIso A x (ForgetEnrichment.to (Complex A) N)).symm

/-- この性質は主加群圏の真の同型で不変。 -/
lemma moduleHomotopicallyProjective_of_iso {M P : ModuleCategory A D} (e : M ≅ P)
    (hM : moduleHomotopicallyProjective A D M) : moduleHomotopicallyProjective A D P := by
  intro N hN i
  exact (hM N hN i).of_iso
    (((eHomFunctor (Complex A) (ModuleCategory A D)).mapIso e.op).app N).symm

instance moduleHomotopicallyProjectiveClosedUnderIso :
    (moduleHomotopicallyProjective A D).IsClosedUnderIsomorphisms where
  of_iso := moduleHomotopicallyProjective_of_iso A D

/-- 零加群も Hom end の意味で homotopically projective。 -/
lemma moduleHomotopicallyProjective_of_isZero {M : ModuleCategory A D} (hM : IsZero M) :
    moduleHomotopicallyProjective A D M := by
  intro N _ i
  have hz := moduleHom_isZero_src A D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) N) ((module_isZero_iff A D M).1 hM)
  exact HomologicalComplex.ExactAt.of_isZero
    ((HomologicalComplex.eval (ModuleCat A) (.up ℤ) i).map_isZero hz)

end SerrePositivity.DifferentialGraded
end

end HomotopicallyProjective

/-! ## FreeProjective（旧 SerrePositivity/DifferentialGraded/Derived/FreeProjective.lean） -/

/-! K-projective 係数を持つ自由 dg 加群の全 Hom 射影性。 -/

@[expose] public section FreeProjective
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma freeAt_homotopicallyProjective (x : D) (K : Complex A) [K.IsKProjective] :
    moduleHomotopicallyProjective A D ((freeAt x).obj K) := by
  intro N hN
  exact cochainAcyclic_of_iso
    (homComplex_acyclic_of_isKProjective A K ((moduleEvaluation A D x).obj N) (hN x))
    (freeHomIso A D x K (ForgetEnrichment.to (Complex A) N)).symm

end SerrePositivity.DifferentialGraded
end

end FreeProjective

/-! ## FreeSphereProjective（旧 SerrePositivity/DifferentialGraded/Derived/FreeSphereProjective.lean） -/

/-! # 自由sphereはHom endの意味でhomotopically projective

各評価のK-projective性ではなく、free/evaluationの全次数Hom同型から証明する。
-/

@[expose] public section FreeSphereProjective
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma freeSphere_homotopicallyProjective (x : D) (n : ℤ) :
    moduleHomotopicallyProjective A D (freeSphere A D x n) := by
  intro N hN i
  exact (complexSphereHom_acyclic A ((moduleEvaluation A D x).obj N) n (hN x) i).of_iso
    (freeHomIso A D x (complexSphere A n) (ForgetEnrichment.to (Complex A) N)).symm

end SerrePositivity.DifferentialGraded
end

end FreeSphereProjective

/-! ## ProjectiveHomotopy（旧 SerrePositivity/DifferentialGraded/Derived/ProjectiveHomotopy.lean） -/

/-! # 射影的な始域からacyclic加群への全dg自然なホモトピー -/

@[expose] public section ProjectiveHomotopy
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleHomotopicallyProjective_homotopy {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleAcyclic A D N)
    (f g : M ⟶ N) : Nonempty (ModuleHomotopy A D f g) := by
  let K := moduleHom A D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) N)
  let zf := cycleFromUnit K (ForgetEnrichment.homTo (Complex A) f)
  let zg := cycleFromUnit K (ForgetEnrichment.homTo (Complex A) g)
  have hz : K.d 0 1 (zf.val - zg.val) = 0 := by
    rw [map_sub, zf.property, zg.property, sub_self]
  obtain ⟨h, dh⟩ := complexAcyclic_boundary (K := K) (hM N hN) 0 (zf.val - zg.val) hz
  exact ⟨⟨h, dh⟩⟩

lemma moduleHomotopicallyProjective_homotopy_map_eq {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleAcyclic A D N)
    (f g : M ⟶ N) : (moduleToHomotopy A D).map f = (moduleToHomotopy A D).map g :=
  (moduleToHomotopy_map_eq_iff A D f g).2
    (moduleHomotopicallyProjective_homotopy A D hM hN f g)

end SerrePositivity.DifferentialGraded
end

end ProjectiveHomotopy

/-! ## ProjectiveContraction（旧 SerrePositivity/DifferentialGraded/Derived/ProjectiveContraction.lean） -/

/-! # ホモトピー射影的かつ非輪状な加群の明示的収縮

全次数 Hom end の非輪状性により、恒等の次数 −1 の原像を取る。
収縮は全 dg 作用と自然であり、対象別の収縮の選択を並べるものではない。
-/

@[expose] public section ProjectiveContraction
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- ホモトピー射影的かつ対象ごと非輪状な加群の恒等は、実 Hom end の境界である。 -/
theorem moduleHomotopicallyProjective_contractingElement_of_acyclic
    (M : RightModule R D)
    (hM : moduleHomotopicallyProjective R D (ForgetEnrichment.of (Complex R) M))
    (hA : moduleAcyclic R D (ForgetEnrichment.of (Complex R) M)) :
    ∃ H : GradedHom R M M (-1),
      (homObject R (RightModule R D) M M).d (-1) 0 H = (unitElement R M).val := by
  exact complexAcyclic_boundary (hM _ hA) 0 (unitElement R M).val (differential_unit R M)

end SerrePositivity.DifferentialGraded
end

end ProjectiveContraction

/-! ## CoproductProjective（旧 SerrePositivity/DifferentialGraded/Derived/CoproductProjective.lean） -/

/-! # 余積・自由sphere表示のhomotopically projective性 -/

@[expose] public section CoproductProjective
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleCoproduct_homotopicallyProjective {J : Type w} [Small.{u} J]
    (M : J → ModuleCategory A D) (hM : ∀ j, moduleHomotopicallyProjective A D (M j)) :
    moduleHomotopicallyProjective A D (∐ M) := by
  intro N hN i
  exact (complexProduct_acyclic A (moduleCoproductHomFamily A D M N)
    (fun j => hM j N hN) i).of_iso (moduleCoproductHomIso A D M N).symm

lemma ModuleSphereFreePresentation.homotopicallyProjective {M : ModuleCategory A D}
    (S : ModuleSphereFreePresentation A D M) : moduleHomotopicallyProjective A D M := by
  let : Small.{u} S.Index := S.smallIndex
  exact moduleHomotopicallyProjective_of_iso A D S.iso.symm
    (moduleCoproduct_homotopicallyProjective A D _
      (fun t => freeSphere_homotopicallyProjective A D (S.object t) (S.degree t)))

lemma ModuleSemifreeFiltration.initial_homotopicallyProjective {M : ModuleCategory A D}
    (F : ModuleSemifreeFiltration A D M) : moduleHomotopicallyProjective A D (F.stage 0) :=
  F.initial.homotopicallyProjective A D

lemma ModuleSemifreeFiltration.quotient_homotopicallyProjective {M : ModuleCategory A D}
    (F : ModuleSemifreeFiltration A D M) (n : ℕ) :
    moduleHomotopicallyProjective A D (F.quotient n) :=
  (F.quotientPresentation n).homotopicallyProjective A D

end SerrePositivity.DifferentialGraded
end

end CoproductProjective

/-! ## GradedExtensionProjective（旧 SerrePositivity/DifferentialGraded/Derived/GradedExtensionProjective.lean） -/

/-! # 全次数分裂する拡大とsemifree filtrationの有限段の射影性 -/

@[expose] public section GradedExtensionProjective
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma ModuleGradedSplit.homotopicallyProjective {M N P : ModuleCategory A D}
    {f : M ⟶ N} {g : N ⟶ P} (s : ModuleGradedSplit A D f g)
    (hM : moduleHomotopicallyProjective A D M)
    (hP : moduleHomotopicallyProjective A D P) :
    moduleHomotopicallyProjective A D N := by
  intro T hT
  exact (s.homShortComplex_shortExact T).acyclic_X₂ (hP T hT) (hM T hT)

lemma ModuleSemifreeFiltration.stage_homotopicallyProjective {M : ModuleCategory A D}
    (F : ModuleSemifreeFiltration A D M) (n : ℕ) :
    moduleHomotopicallyProjective A D (F.stage n) := by
  induction n with
  | zero => exact F.initial_homotopicallyProjective A D
  | succ n ih =>
    exact (F.split n).homotopicallyProjective A D ih (F.quotient_homotopicallyProjective A D n)

end SerrePositivity.DifferentialGraded
end

end GradedExtensionProjective

/-! ## SemifreeProjective（旧 SerrePositivity/DifferentialGraded/Derived/SemifreeProjective.lean） -/

/-! # semifree加群のhomotopically projective性

各有限段のHom acyclic性、Hom制限の全射性と実際の極限普遍性を接続する。
-/

@[expose] public section SemifreeProjective
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma ModuleSemifreeFiltration.homotopicallyProjective {M : ModuleCategory A D}
    (F : ModuleSemifreeFiltration A D M) : moduleHomotopicallyProjective A D M := by
  apply moduleHomotopicallyProjective_of_iso A D F.iso
  intro T hT
  apply complexTowerLimit_acyclic A
    (moduleHomSourceDiagram A D (Functor.ofSequence F.transition) T)
    (moduleColimitHomIsLimit A D F.isColimit T)
  · intro n
    exact F.stage_homotopicallyProjective A D n T hT
  · intro n q
    change Function.Surjective
      ((eHomWhiskerRight (Complex A)
        ((Functor.ofSequence F.transition).map (homOfLE (n.le_add_right 1))) T).f q)
    rw [Functor.ofSequence_map_homOfLE_succ]
    exact (F.split n).homRestriction_surjective T q

lemma moduleSemifree_homotopicallyProjective {M : ModuleCategory A D}
    (hM : moduleSemifree A D M) : moduleHomotopicallyProjective A D M := by
  obtain ⟨F⟩ := hM
  exact F.homotopicallyProjective A D

theorem exists_homotopicallyProjective_resolution (M : ModuleCategory A D) :
    ∃ (P : ModuleCategory A D) (q : P ⟶ M),
      moduleHomotopicallyProjective A D P ∧
        moduleDegreewiseSurjective A D q ∧ moduleQuasiIso A D q := by
  obtain ⟨P, q, hP, hq, hW⟩ := exists_semifree_resolution A D M
  exact ⟨P, q, moduleSemifree_homotopicallyProjective A D hP, hq, hW⟩

end SerrePositivity.DifferentialGraded
end

end SemifreeProjective

/-! ## RestrictionProjective（旧 SerrePositivity/DifferentialGraded/Derived/RestrictionProjective.lean） -/

/-!
概要：生成 sphere の実制限の射影性から semifree 加群の実制限の射影性を得る。
方針：全次数分裂の有限段と全射 Hom tower の実極限を使う。
規約：K-flat 性だけから射影性を推論しない。
使われ方：積 dg 圏上の固定 bimodule 解像度の各右制限。
-/

@[expose] public section RestrictionProjective
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [DGCategory A E] [Small.{u} D] [Small.{u} E]
  (F : DGFunctor A Dᵒᵖ Eᵒᵖ)

lemma ModuleSphereFreePresentation.restriction_homotopicallyProjective
    (hfree : ∀ (x : E) (n : ℤ), moduleHomotopicallyProjective A D
      ((moduleRestriction A D E F).obj (freeSphere A E x n)))
    {M : ModuleCategory A E} (S : ModuleSphereFreePresentation A E M) :
    moduleHomotopicallyProjective A D ((moduleRestriction A D E F).obj M) := by
  have := S.smallIndex
  let e := PreservesCoproduct.iso (moduleRestriction A D E F)
    (fun t => freeSphere A E (S.object t) (S.degree t))
  exact moduleHomotopicallyProjective_of_iso A D
    (((moduleRestriction A D E F).mapIso S.iso) ≪≫ e).symm
    (moduleCoproduct_homotopicallyProjective A D _
      (fun t => hfree (S.object t) (S.degree t)))

lemma ModuleSemifreeFiltration.restriction_stage_homotopicallyProjective
    (hfree : ∀ (x : E) (n : ℤ), moduleHomotopicallyProjective A D
      ((moduleRestriction A D E F).obj (freeSphere A E x n)))
    {M : ModuleCategory A E} (S : ModuleSemifreeFiltration A E M) (n : ℕ) :
    moduleHomotopicallyProjective A D ((moduleRestriction A D E F).obj (S.stage n)) := by
  induction n with
  | zero => exact S.initial.restriction_homotopicallyProjective A D E F hfree
  | succ n ih =>
    exact ((S.split n).restrict A D E F).homotopicallyProjective A D ih
      ((S.quotientPresentation n).restriction_homotopicallyProjective A D E F hfree)

lemma ModuleSemifreeFiltration.restriction_homotopicallyProjective
    (hfree : ∀ (x : E) (n : ℤ), moduleHomotopicallyProjective A D
      ((moduleRestriction A D E F).obj (freeSphere A E x n)))
    {M : ModuleCategory A E} (S : ModuleSemifreeFiltration A E M) :
    moduleHomotopicallyProjective A D ((moduleRestriction A D E F).obj M) := by
  apply moduleHomotopicallyProjective_of_iso A D ((moduleRestriction A D E F).mapIso S.iso)
  intro T hT
  apply complexTowerLimit_acyclic A
    (moduleHomSourceDiagram A D
      (Functor.ofSequence S.transition ⋙ moduleRestriction A D E F) T)
    (moduleColimitHomIsLimit A D
      (moduleRestrictionIsColimit A D E F S.cocone S.isColimit) T)
  · intro n
    exact S.restriction_stage_homotopicallyProjective A D E F hfree n T hT
  · intro n q
    change Function.Surjective
      ((eHomWhiskerRight (Complex A)
        ((moduleRestriction A D E F).map
          ((Functor.ofSequence S.transition).map (homOfLE (n.le_add_right 1)))) T).f q)
    rw [Functor.ofSequence_map_homOfLE_succ]
    exact ((S.split n).restrict A D E F).homRestriction_surjective T q

lemma moduleSemifree_restriction_homotopicallyProjective
    (hfree : ∀ (x : E) (n : ℤ), moduleHomotopicallyProjective A D
      ((moduleRestriction A D E F).obj (freeSphere A E x n)))
    {M : ModuleCategory A E} (hM : moduleSemifree A E M) :
    moduleHomotopicallyProjective A D ((moduleRestriction A D E F).obj M) := by
  obtain ⟨S⟩ := hM
  exact S.restriction_homotopicallyProjective A D E F hfree

end SerrePositivity.DifferentialGraded
end

end RestrictionProjective

/-! ## ProjectiveFiniteOperations（旧 SerrePositivity/DifferentialGraded/Derived/ProjectiveFiniteOperations.lean） -/

/-! # 主Homによる射影性の有限操作に対する閉性 -/

@[expose] public section ProjectiveFiniteOperations
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 主Hom endの始域shiftは、通常の複体の逆shiftに対応する。 -/
def moduleHomSourceShiftIso (M N : RightModule A D) (s : ℤ) :
    moduleHom A D (shiftModule s M) N ≅ (moduleHom A D M N)⟦-s⟧ :=
  DGFunctor.moduleShiftOppImageIso A D
    ((representable A (D := RightModule A D) N).toFunctor) s M

lemma moduleHomotopicallyProjective_shift {M : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (s : ℤ) :
    moduleHomotopicallyProjective A D (M⟦s⟧) := by
  intro N hN
  exact cochainAcyclic_of_iso (cochainAcyclic_shift (hM N hN) (-s))
    (moduleHomSourceShiftIso A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N) s).symm

lemma moduleHomotopicallyProjective_cone {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    (f : M ⟶ N) : moduleHomotopicallyProjective A D (moduleCone A D f) :=
  (moduleConeGradedSplit A D f).homotopicallyProjective A D hN
    (moduleHomotopicallyProjective_shift A D hM 1)

lemma moduleHomotopicallyProjective_biprod {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N) :
    moduleHomotopicallyProjective A D (moduleBiprod A D M N) := by
  have hσ := moduleCoproduct_homotopicallyProjective A D
    (fun j : WalkingPair => WalkingPair.casesOn j M N) (by
      intro j
      cases j
      · exact hM
      · exact hN)
  change moduleHomotopicallyProjective A D (M ⨿ N) at hσ
  exact moduleHomotopicallyProjective_of_iso A D
    ((biprod.isoCoprod M N).symm ≪≫ (moduleBiprodIso A D M N).symm) hσ

end SerrePositivity.DifferentialGraded
end

end ProjectiveFiniteOperations
