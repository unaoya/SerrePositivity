module

public import SerrePositivity.DifferentialGraded.Bimodule.Value
public import Mathlib.CategoryTheory.Localization.HasLocalization
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtension.BalancedTensor
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import SerrePositivity.DifferentialGraded.Derived.Projective
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.KFlatness
public import SerrePositivity.DifferentialGraded.Tensor.Graded
public import SerrePositivity.HomologicalAlgebra.RestrictedBaseChangeComplex
public import SerrePositivity.DifferentialGraded.Derived.Tensor

/-!
# Derived.ScalarExtension

## 概要
11 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## BimoduleBasic（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleBasic.lean） -/

/-! # 値ごとのquasiIsoの標準局所化による導来bimodule圏

## 概要
全Hom自然な閉零bimodule射を局所化する。局所化の標準の大きい射宇宙を保持し、
小さいHomや射影モデル構造の存在はこの定義の前提にしない。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleSemifreeComparison.lean、Derived/
BimoduleTensor.lean。固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleBasic
universe u v w z z'

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 指定した値ごとの準同型を局所化した導来bimodule圏。 -/
abbrev DerivedBimoduleCategory := (BimoduleCategory.quasiIso A B C).Localization

/-- 元の全dg自然な閉零bimodule圏からの指定局所化関手。 -/
abbrev bimoduleToDerived : BimoduleCategory A B C ⥤ DerivedBimoduleCategory A B C :=
  (BimoduleCategory.quasiIso A B C).Q

lemma bimoduleToDerived_inverts :
    (BimoduleCategory.quasiIso A B C).IsInvertedBy (bimoduleToDerived A B C) :=
  Localization.inverts _ _

def bimoduleDerivedIso {M N : BimoduleCategory A B C} (f : M ⟶ N)
    (hf : BimoduleCategory.quasiIso A B C f) :
    (bimoduleToDerived A B C).obj M ≅ (bimoduleToDerived A B C).obj N :=
  Localization.Construction.wIso (W := BimoduleCategory.quasiIso A B C) f hf

variable {T : Type z} [Category.{z'} T]

/-- 指定準同型を反転する関手の、標準局所化への延長。 -/
def bimoduleDerivedLift (G : BimoduleCategory A B C ⥤ T)
    (hG : (BimoduleCategory.quasiIso A B C).IsInvertedBy G) :
    DerivedBimoduleCategory A B C ⥤ T := Localization.Construction.lift G hG

lemma bimoduleDerivedLift_fac (G : BimoduleCategory A B C ⥤ T)
    (hG : (BimoduleCategory.quasiIso A B C).IsInvertedBy G) :
    bimoduleToDerived A B C ⋙ bimoduleDerivedLift A B C G hG = G :=
  Localization.Construction.fac G hG

lemma bimoduleDerivedLift_unique (G H : DerivedBimoduleCategory A B C ⥤ T)
    (h : bimoduleToDerived A B C ⋙ G = bimoduleToDerived A B C ⋙ H) : G = H :=
  Localization.Construction.uniq G H h

lemma bimoduleDerivedNatTrans_ext {G H : DerivedBimoduleCategory A B C ⥤ T} {a b : G ⟶ H}
    (h : ∀ M, a.app ((bimoduleToDerived A B C).obj M) =
      b.app ((bimoduleToDerived A B C).obj M)) : a = b :=
  Localization.natTrans_ext (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C) h

end SerrePositivity.DifferentialGraded
end

end BimoduleBasic

/-! ## BimoduleLiftIso（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleLiftIso.lean） -/

/-! # 指定局所化への前合成で与えた自然同型を全導来bimodule圏へ移す

## 概要
指定局所化への前合成で与えた自然同型を全導来bimodule圏へ移す。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleLiftIso
universe u v w z z'

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] {T : Type z} [Category.{z'} T]

/-- 局所化への前合成上の自然同型を、指定された二つの導来関手の間へ降ろす。 -/
def bimoduleDerivedIsoOfPrecomp (G H : DerivedBimoduleCategory A B C ⥤ T)
    (e : bimoduleToDerived A B C ⋙ G ≅ bimoduleToDerived A B C ⋙ H) : G ≅ H := by
  letI sourceLifting : Localization.Lifting (bimoduleToDerived A B C)
      (BimoduleCategory.quasiIso A B C) (bimoduleToDerived A B C ⋙ G) G := ⟨Iso.refl _⟩
  letI targetLifting : Localization.Lifting (bimoduleToDerived A B C)
      (BimoduleCategory.quasiIso A B C) (bimoduleToDerived A B C ⋙ H) H := ⟨Iso.refl _⟩
  exact Localization.liftNatIso (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
    (bimoduleToDerived A B C ⋙ G) (bimoduleToDerived A B C ⋙ H) G H e

lemma bimoduleDerivedIsoOfPrecomp_hom_app (G H : DerivedBimoduleCategory A B C ⥤ T)
    (e : bimoduleToDerived A B C ⋙ G ≅ bimoduleToDerived A B C ⋙ H)
    (P : BimoduleCategory A B C) :
    (bimoduleDerivedIsoOfPrecomp A B C G H e).hom.app ((bimoduleToDerived A B C).obj P) =
      e.hom.app P := by
  simp only [bimoduleDerivedIsoOfPrecomp, Localization.liftNatIso_hom,
    Localization.liftNatTrans_app]
  change 𝟙 _ ≫ e.hom.app P ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]

lemma bimoduleDerivedIsoOfPrecomp_inv_app (G H : DerivedBimoduleCategory A B C ⥤ T)
    (e : bimoduleToDerived A B C ⋙ G ≅ bimoduleToDerived A B C ⋙ H)
    (P : BimoduleCategory A B C) :
    (bimoduleDerivedIsoOfPrecomp A B C G H e).inv.app ((bimoduleToDerived A B C).obj P) =
      e.inv.app P := by
  simp only [bimoduleDerivedIsoOfPrecomp, Localization.liftNatIso_inv,
    Localization.liftNatTrans_app]
  change 𝟙 _ ≫ e.inv.app P ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]

end SerrePositivity.DifferentialGraded
end

end BimoduleLiftIso

/-! ## ScalarExtensionHomotopy（旧 SerrePositivity/DifferentialGraded/Derived/ScalarExtensionHomotopy.lean） -/

/-! # 非 flat な係数拡大と加群ホモトピー

標準 cylinder の射影だけを反転して境界を同一視する。
任意の擬同型を underived 係数拡大が保存するとは仮定しない。
-/

@[expose] public section ScalarExtensionHomotopy
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory HomologicalComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 標準 cylinder の射影は任意の係数変更後も擬同型。 -/
lemma moduleExtension_cylinder_quasiIso (M : ModuleCategory A D) :
    moduleQuasiIso A' (DGBaseChange φ D)
      ((moduleExtension φ D).map (modulePrecylinder A D M).π) := by
  intro x
  rw [moduleExtension_eval]
  change QuasiIso ((extension φ).map ((moduleEvaluation A D x).map
    (tensorModuleMap (cylinder.π (𝟙_ (Complex A))) (ForgetEnrichment.to (Complex A) M) ≫
      (moduleTensorUnitIso A D (ForgetEnrichment.to (Complex A) M)).hom)))
  rw [CategoryTheory.Functor.map_comp, tensorModuleMap_eval, moduleTensorUnitIso_hom_eval,
    CategoryTheory.Functor.map_comp]
  have : QuasiIso ((extension φ).map
      (cylinder.π (𝟙_ (Complex A)) ⊗ₘ
        𝟙 ((ForgetEnrichment.to (Complex A) M).obj (Opposite.op x)))) :=
    ((ModuleCat.extendScalars φ).mapHomotopyEquiv
      (tensorIntervalHomotopyEquiv A
        ((ForgetEnrichment.to (Complex A) M).obj (Opposite.op x)))).quasiIso_hom
  infer_instance

/-- 係数拡大後の主導来圏では、元の全 dg 自然な境界が等しくなる。 -/
lemma moduleExtension_equalizes_boundary {M N : ModuleCategory A D} (f g : M ⟶ N)
    (h : boundaryRelation A (RightModule A D) f g) :
    (moduleToDerived A' (DGBaseChange φ D)).map ((moduleExtension φ D).map f) =
      (moduleToDerived A' (DGBaseChange φ D)).map ((moduleExtension φ D).map g) := by
  let F := moduleExtension φ D ⋙ moduleToDerived A' (DGBaseChange φ D)
  let P := modulePrecylinder A D M
  let H := moduleCylinderLeftHomotopy A D f g h
  let e := @asIso (DerivedModuleCategory A' (DGBaseChange φ D)) _ _ _ (F.map P.π)
    (moduleToDerived_inverts A' (DGBaseChange φ D) _
      (moduleExtension_cylinder_quasiIso φ D M))
  have hi : F.map P.i₀ = F.map P.i₁ := by
    have hs : F.map P.i₀ ≫ e.hom = F.map P.i₁ ≫ e.hom := by
      change F.map P.i₀ ≫ F.map P.π = F.map P.i₁ ≫ F.map P.π
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, P.i₀_π, P.i₁_π]
    have hc := congrArg (fun k => k ≫ e.inv) hs
    simpa only [Category.assoc, e.hom_inv_id, Category.comp_id] using hc
  change F.map f = F.map g
  calc
    F.map f = F.map (P.i₀ ≫ H.h) := congrArg F.map H.h₀.symm
    _ = F.map P.i₀ ≫ F.map H.h := F.map_comp _ _
    _ = F.map P.i₁ ≫ F.map H.h := congrArg (fun k => k ≫ F.map H.h) hi
    _ = F.map g := (F.map_comp _ _).symm.trans (congrArg F.map H.h₁)

/-- 任意の係数変更を K(D) から係数変更後の主導来圏へ送る。 -/
def moduleExtensionHomotopyToDerived : ModuleHomotopyCategory A D ⥤
    DerivedModuleCategory A' (DGBaseChange φ D) :=
  CategoryTheory.Quotient.lift _
    (moduleExtension φ D ⋙ moduleToDerived A' (DGBaseChange φ D))
    (fun _ _ f g h => moduleExtension_equalizes_boundary φ D f g h)

lemma moduleExtensionHomotopyToDerived_fac :
    moduleToHomotopy A D ⋙ moduleExtensionHomotopyToDerived φ D =
      moduleExtension φ D ⋙ moduleToDerived A' (DGBaseChange φ D) :=
  CategoryTheory.Quotient.lift_spec _ _ _

lemma moduleExtension_map_eq_of_homotopy {M N : ModuleCategory A D} (f g : M ⟶ N)
    (h : (moduleToHomotopy A D).map f = (moduleToHomotopy A D).map g) :
    (moduleToDerived A' (DGBaseChange φ D)).map ((moduleExtension φ D).map f) =
      (moduleToDerived A' (DGBaseChange φ D)).map ((moduleExtension φ D).map g) :=
  congrArg (moduleExtensionHomotopyToDerived φ D).map h

end SerrePositivity.DifferentialGraded.ScalarExtension
end

end ScalarExtensionHomotopy

/-! ## ScalarExtension（旧 SerrePositivity/DifferentialGraded/Derived/ScalarExtension.lean） -/

/-! # 任意の環準同型による導来係数拡大

全 dg 自然な射影解像度を K(D) へ取り、係数変更後の主導来圏へ送る。
係数環の flatness も元の dg 圏の local flatness も要求しない。
-/

@[expose] public section ScalarExtension
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 指定した射影解像度族による非 flat な導来係数拡大。 -/
def resolutionDerivedExtension
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    DerivedModuleCategory A D ⥤ DerivedModuleCategory A' (DGBaseChange φ D) :=
  moduleDerivedResolutionFunctor A D R ⋙ moduleExtensionHomotopyToDerived φ D

/-- 標準 semifree 解像度による導来係数拡大。 -/
def derivedExtension :
    DerivedModuleCategory A D ⥤ DerivedModuleCategory A' (DGBaseChange φ D) :=
  resolutionDerivedExtension φ D (moduleCanonicalProjectiveResolution A D)

/-- 指定解像度による実際の計算式。 -/
def resolutionDerivedExtensionComputation
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) (M : ModuleCategory A D) :
    (resolutionDerivedExtension φ D R).obj ((moduleToDerived A D).obj M) ≅
      (moduleToDerived A' (DGBaseChange φ D)).obj ((moduleExtension φ D).obj (R M).obj) :=
  (moduleExtensionHomotopyToDerived φ D).mapIso (moduleDerivedResolutionComputation A D R M)

/-- 解像度選択の変更は自然同型を与える。 -/
def resolutionDerivedExtensionIso
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    resolutionDerivedExtension φ D R ≅ resolutionDerivedExtension φ D S :=
  Functor.isoWhiskerRight (moduleDerivedResolutionIso A D R S)
    (moduleExtensionHomotopyToDerived φ D)

lemma resolutionDerivedExtensionIso_self
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    resolutionDerivedExtensionIso φ D R R = Iso.refl _ := by
  unfold resolutionDerivedExtensionIso
  rw [moduleDerivedResolutionIso_self]
  apply Iso.ext
  apply NatTrans.ext
  funext X
  exact (moduleExtensionHomotopyToDerived φ D).map_id _

lemma resolutionDerivedExtensionIso_trans
    (R S T : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    resolutionDerivedExtensionIso φ D R S ≪≫ resolutionDerivedExtensionIso φ D S T =
      resolutionDerivedExtensionIso φ D R T := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  change (moduleExtensionHomotopyToDerived φ D).map
      ((moduleDerivedResolutionIso A D R S).hom.app X) ≫
    (moduleExtensionHomotopyToDerived φ D).map
      ((moduleDerivedResolutionIso A D S T).hom.app X) = _
  rw [← CategoryTheory.Functor.map_comp]
  exact congrArg (moduleExtensionHomotopyToDerived φ D).map
    (NatTrans.congr_app (congrArg Iso.hom (moduleDerivedResolutionIso_trans A D R S T)) X)

/-- 任意の証明付き射影解像度で標準導来係数拡大を計算できる。 -/
def derivedExtensionResolutionComputation {M : ModuleCategory A D}
    (P : ModuleProjectiveResolution A D M) :
    (derivedExtension φ D).obj ((moduleToDerived A D).obj M) ≅
      (moduleToDerived A' (DGBaseChange φ D)).obj ((moduleExtension φ D).obj P.obj) := by
  let R := moduleCanonicalProjectiveResolution A D
  exact resolutionDerivedExtensionComputation φ D R M ≪≫
    (moduleExtensionHomotopyToDerived φ D).mapIso
      (@asIso _ _ _ _ ((moduleToHomotopy A D).map ((R M).comparison P))
        ((R M).comparison_isIso_homotopy P))

/-- underived 比較射。これを同型とするには増大射の係数変更後の擬同型性が必要。 -/
def derivedExtensionComparison {M : ModuleCategory A D}
    (P : ModuleProjectiveResolution A D M) :
    (derivedExtension φ D).obj ((moduleToDerived A D).obj M) ⟶
      (moduleToDerived A' (DGBaseChange φ D)).obj ((moduleExtension φ D).obj M) :=
  (derivedExtensionResolutionComputation φ D P).hom ≫
    (moduleToDerived A' (DGBaseChange φ D)).map ((moduleExtension φ D).map P.π)

/-- 増大射が係数変更後も擬同型なら underived 比較は同型。 -/
lemma derivedExtensionComparison_isIso {M : ModuleCategory A D}
    (P : ModuleProjectiveResolution A D M)
    (hπ : moduleQuasiIso A' (DGBaseChange φ D) ((moduleExtension φ D).map P.π)) :
    IsIso (derivedExtensionComparison φ D P) := by
  have := moduleToDerived_inverts A' (DGBaseChange φ D) _ hπ
  unfold derivedExtensionComparison
  infer_instance

end SerrePositivity.DifferentialGraded.ScalarExtension
end

end ScalarExtension

/-! ## ScalarExtensionExact（旧 SerrePositivity/DifferentialGraded/Derived/ScalarExtensionExact.lean） -/

/-! # underived 係数変更による擬同型保存の条件

係数制限は無条件で exact。係数拡大はホモロジー保存を明示し、
環準同型の flatness をその十分条件として与える。
-/

@[expose] public section ScalarExtensionExact
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory HomologicalComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

lemma restriction_quasiIso {K L : Complex A'} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((restriction φ).map f) := by
  change QuasiIso (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).map f)
  infer_instance

lemma moduleRestriction_quasiIso {M N : ModuleCategory A' (DGBaseChange φ D)}
    (f : M ⟶ N) (hf : moduleQuasiIso A' (DGBaseChange φ D) f) :
    moduleQuasiIso A D ((moduleRestriction φ D).map f) := by
  intro x
  rw [moduleRestriction_eval]
  have := hf x
  exact restriction_quasiIso φ _

/-- 係数制限は非 flat な環準同型でも主導来加群圏へ降りる。 -/
def derivedRestriction : DerivedModuleCategory A' (DGBaseChange φ D) ⥤
    DerivedModuleCategory A D :=
  moduleDerivedLift A' (DGBaseChange φ D)
    (moduleRestriction φ D ⋙ moduleToDerived A D) (by
      intro M N f hf
      exact moduleToDerived_inverts A D _ (moduleRestriction_quasiIso φ D f hf))

lemma derivedRestriction_fac :
    moduleToDerived A' (DGBaseChange φ D) ⋙ derivedRestriction φ D =
      moduleRestriction φ D ⋙ moduleToDerived A D := moduleDerivedLift_fac _ _ _ _

/-- 一般の擬同型を underived に送る十分条件は exactness。 -/
lemma extension_quasiIso_of_preservesHomology
    [(ModuleCat.extendScalars φ).PreservesHomology]
    {K L : Complex A} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((extension φ).map f) := by
  change QuasiIso (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map f)
  infer_instance

lemma extension_quasiIso_of_flat (hφ : φ.Flat) {K L : Complex A} (f : K ⟶ L)
    [QuasiIso f] : QuasiIso ((extension φ).map f) := by
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ
  exact extension_quasiIso_of_preservesHomology φ f

lemma moduleExtension_quasiIso_of_flat (hφ : φ.Flat) {M N : ModuleCategory A D}
    (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    moduleQuasiIso A' (DGBaseChange φ D) ((moduleExtension φ D).map f) := by
  intro x
  rw [moduleExtension_eval]
  have := hf x
  exact extension_quasiIso_of_flat φ hφ _

/-- flat な場合は解像度の増大射の係数変更も擬同型となる。 -/
lemma derivedExtensionComparison_isIso_of_flat (hφ : φ.Flat)
    {M : ModuleCategory A D} (P : ModuleProjectiveResolution A D M) :
    IsIso (derivedExtensionComparison φ D P) :=
  derivedExtensionComparison_isIso φ D P
    (moduleExtension_quasiIso_of_flat φ D hφ P.π P.quasiIso)

end SerrePositivity.DifferentialGraded.ScalarExtension
end

end ScalarExtensionExact

/-! ## ScalarExtensionKFlat（旧 SerrePositivity/DifferentialGraded/Derived/ScalarExtensionKFlat.lean） -/

/-! # 非 flat な係数変更と K-flat 複体

擬同型の両端が A 上 K-flat なら、係数環の flatness は不要。
dg 加群の相対 K-flat 性と評価ごとの A-K-flat 性は区別する。
-/

@[expose] public section ScalarExtensionKFlat
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory HomologicalComplex Opposite
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

omit φ in
lemma ringModule_relativeKFlat {K : Complex A} (hK : complexKFlat A K) :
    moduleRelativeKFlat A PUnit.{1} (ringModule A K) := by
  intro L hL
  exact cochainAcyclic_of_iso (hK (L.obj PUnit.unit) (hL PUnit.unit))
    (BalancedTensor.ringIso A (ringModule A K) L).symm

omit φ in
/-- 両端 K-flat な擬同型は、任意の複体との tensor で擬同型。 -/
lemma tensor_quasiIso_of_kFlat_ends {K L : Complex A}
    (hK : complexKFlat A K) (hL : complexKFlat A L) (f : K ⟶ L) [QuasiIso f]
    (T : Complex A) : QuasiIso (cochainTensorMap f (𝟙 T)) := by
  let M := ForgetEnrichment.of (Complex A) (ringModule A K)
  let N := ForgetEnrichment.of (Complex A) (ringModule A L)
  let E := moduleEvaluation A PUnit.{1} PUnit.unit
  let g : M ⟶ N := E.preimage f
  have hg : E.map g = f := E.map_preimage (X := M) (Y := N) f
  have hq : moduleQuasiIso A PUnit.{1} g :=
    (ringModuleQuasiIso_iff A g).2 (by rw [hg]; infer_instance)
  have ht := BalancedTensor.rightTensor_relativeKFlat_quasiIso A PUnit.{1}
    (ringLeftModule A T) (ringModule_relativeKFlat hK) (ringModule_relativeKFlat hL) g hq
  let V := ForgetEnrichment.of (Complex A) (ringLeftModule A T)
  have hn := BalancedTensor.ringIso_naturality A g (𝟙 V)
  simp only [CategoryTheory.Functor.map_id] at hn
  change BalancedTensor.map A PUnit.{1} g (𝟙 V) ≫ _ = _ ≫ (E.map g ⊗ₘ 𝟙 T) at hn
  rw [hg] at hn
  have : QuasiIso (BalancedTensor.map A PUnit.{1} g (𝟙 V)) := ht
  have hc : QuasiIso ((BalancedTensor.ringIso A (ringModule A K) (ringLeftModule A T)).hom ≫
      cochainTensorMap f (𝟙 T)) := by
    change QuasiIso ((BalancedTensor.ringIso A (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) V)).hom ≫ (f ⊗ₘ 𝟙 T))
    rw [← hn]
    infer_instance
  exact quasiIso_of_comp_left (BalancedTensor.ringIso A (ringModule A K) (ringLeftModule A T)).hom _

/-- K-flat な両端の擬同型に対する非 flat 係数拡大の保存。 -/
lemma extension_quasiIso_of_kFlat_ends {K L : Complex A}
    (hK : complexKFlat A K) (hL : complexKFlat A L) (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((extension φ).map f) := by
  let T := cochainSingleZero (baseChangeScalarModule φ)
  have ht := tensor_quasiIso_of_kFlat_ends hK hL f T
  have hswap := cochainTensorSymmetry_naturality (𝟙 T) f
  have hc : QuasiIso (cochainTensorMap (𝟙 T) f ≫ (cochainTensorSymmetry T L).hom) := by
    rw [hswap]
    infer_instance
  have : QuasiIso (cochainTensorMap (𝟙 T) f) :=
    quasiIso_of_comp_right _ (cochainTensorSymmetry T L).hom
  have hn := restrictedBaseChangeComplexIso_naturality φ f
  have hc : QuasiIso ((restriction φ).map ((extension φ).map f) ≫
      (restrictedBaseChangeComplexIso φ L).hom) := by
    rw [hn]
    infer_instance
  have : QuasiIso ((restriction φ).map ((extension φ).map f)) :=
    quasiIso_of_comp_right _ (restrictedBaseChangeComplexIso φ L).hom
  exact (quasiIso_map_iff_of_preservesHomology ((extension φ).map f)
    (ModuleCat.restrictScalars φ)).1 this

variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 相対 K-flat 性だけでなく各評価の A-K-flat 性を要求する。 -/
lemma moduleExtension_quasiIso_of_objectwiseKFlat {M N : ModuleCategory A D}
    (hM : moduleObjectwiseKFlat A D (ForgetEnrichment.to (Complex A) M))
    (hN : moduleObjectwiseKFlat A D (ForgetEnrichment.to (Complex A) N))
    (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    moduleQuasiIso A' (DGBaseChange φ D) ((moduleExtension φ D).map f) := by
  intro x
  rw [moduleExtension_eval]
  have := hf x
  exact extension_quasiIso_of_kFlat_ends φ (hM x) (hN x) _

lemma derivedExtensionComparison_isIso_of_objectwiseKFlat {M : ModuleCategory A D}
    (P : ModuleProjectiveResolution A D M)
    (hP : moduleObjectwiseKFlat A D (ForgetEnrichment.to (Complex A) P.obj))
    (hM : moduleObjectwiseKFlat A D (ForgetEnrichment.to (Complex A) M)) :
    IsIso (derivedExtensionComparison φ D P) :=
  derivedExtensionComparison_isIso φ D P
    (moduleExtension_quasiIso_of_objectwiseKFlat φ D hP hM P.π P.quasiIso)

end SerrePositivity.DifferentialGraded.ScalarExtension
end

end ScalarExtensionKFlat

/-! ## ScalarExtensionComplex（旧 SerrePositivity/DifferentialGraded/Derived/ScalarExtensionComplex.lean） -/

/-! # 非有界複体の導来係数拡大

一対象 dg 圏の主導来圏と既存の DerivedCategory の同値を通す。
有界性や係数環の flatness は要求しない。
-/

@[expose] public section ScalarExtensionComplex
universe u w w'

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory HomologicalComplex Opposite
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]
variable [HasDerivedCategory.{w'} (ModuleCat.{u} A')]

/-- 任意の非有界複体に対する導来係数変更。 -/
def complexDerivedExtension : DerivedCategory (ModuleCat.{u} A) ⥤
    DerivedCategory (ModuleCat.{u} A') :=
  (ringDerivedEquivalence A).inverse ⋙ derivedExtension φ PUnit.{1} ⋙
    moduleDerivedEvaluation A' (DGBaseChange φ PUnit.{1}) PUnit.unit

/-- 一対象加群の局所化と複体局所化の比較を逆向きに読む。 -/
def ringDerivedInverseComputation (M : ModuleCategory A PUnit.{1}) :
    (ringDerivedEquivalence A).inverse.obj
        (DerivedCategory.Q.obj ((moduleEvaluation A PUnit.{1} PUnit.unit).obj M)) ≅
      (moduleToDerived A PUnit.{1}).obj M :=
  (ringDerivedEquivalence A).inverse.mapIso ((ringDerivedEquivalence_fac A).app M).symm ≪≫
    ((ringDerivedEquivalence A).unitIso.app ((moduleToDerived A PUnit.{1}).obj M)).symm

/-- 任意の射影加群解像度による非有界複体の計算。 -/
def complexDerivedExtensionComputation (K : Complex A)
    (P : ModuleProjectiveResolution A PUnit.{1}
      (ForgetEnrichment.of (Complex A) (ringModule A K))) :
    (complexDerivedExtension φ).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((extension φ).obj
        ((ForgetEnrichment.to (Complex A) P.obj).obj (op PUnit.unit))) :=
  (derivedExtension φ PUnit.{1} ⋙
      moduleDerivedEvaluation A' (DGBaseChange φ PUnit.{1}) PUnit.unit).mapIso
        (ringDerivedInverseComputation (ForgetEnrichment.of (Complex A) (ringModule A K))) ≪≫
    (moduleDerivedEvaluation A' (DGBaseChange φ PUnit.{1}) PUnit.unit).mapIso
      (derivedExtensionResolutionComputation φ PUnit.{1} P)

/-- A 上 K-flat な複体では、標準 semifree 解像度を外して計算できる。 -/
def complexDerivedExtensionKFlatComputation (K : Complex A) (hK : complexKFlat A K) :
    (complexDerivedExtension φ).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((extension φ).obj K) := by
  let M := ForgetEnrichment.of (Complex A) (ringModule A K)
  let P := moduleCanonicalProjectiveResolution A PUnit.{1} M
  have hP : moduleObjectwiseKFlat A PUnit.{1}
      (ForgetEnrichment.to (Complex A) P.obj) :=
    moduleSemifree_objectwiseKFlat A PUnit.{1} (fun _ _ => complexKFlat_unit A)
      (moduleResolutionCandidate_semifree A PUnit.{1} M)
  let f : (ForgetEnrichment.to (Complex A) P.obj).obj (op PUnit.unit) ⟶ K :=
    (moduleEvaluation A PUnit.{1} PUnit.unit).map P.π
  have : QuasiIso f := P.quasiIso PUnit.unit
  have : QuasiIso ((extension φ).map f) :=
    extension_quasiIso_of_kFlat_ends φ (hP PUnit.unit) hK f
  exact complexDerivedExtensionComputation φ K P ≪≫
    asIso (DerivedCategory.Q.map ((extension φ).map f))

end SerrePositivity.DifferentialGraded.ScalarExtension
end

end ScalarExtensionComplex

/-! ## ScalarExtensionNaturality（旧 SerrePositivity/DifferentialGraded/Derived/ScalarExtensionNaturality.lean） -/

/-! # 導来係数拡大の underived 比較の自然性 -/

@[expose] public section ScalarExtensionNaturality
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 解像度族の増大射は、係数変更後の導来圏で自然。 -/
def resolutionExtensionAugmentation
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionHomotopyFunctor A D R ⋙ moduleExtensionHomotopyToDerived φ D ⟶
      moduleExtension φ D ⋙ moduleToDerived A' (DGBaseChange φ D) where
  app M := (moduleToDerived A' (DGBaseChange φ D)).map ((moduleExtension φ D).map (R M).π)
  naturality {M N} f := by
    have h := congrArg (moduleExtensionHomotopyToDerived φ D).map ((R M).lift_fac (R N) f)
    simp only [CategoryTheory.Functor.map_comp] at h
    convert h using 1 <;> rfl

/-- 主導来関手から underived 係数拡大への自然な比較。
成分が同型かどうかは K-flat 条件によって別に判定する。 -/
def derivedExtensionAugmentation :
    moduleToDerived A D ⋙ derivedExtension φ D ⟶
      moduleExtension φ D ⋙ moduleToDerived A' (DGBaseChange φ D) :=
  Functor.whiskerRight (moduleDerivedResolutionFunctor_fac A D
    (moduleCanonicalProjectiveResolution A D)).hom (moduleExtensionHomotopyToDerived φ D) ≫
      resolutionExtensionAugmentation φ D (moduleCanonicalProjectiveResolution A D)

lemma derivedExtensionAugmentation_app (M : ModuleCategory A D) :
    (derivedExtensionAugmentation φ D).app M =
      (resolutionDerivedExtensionComputation φ D (moduleCanonicalProjectiveResolution A D) M).hom ≫
        (moduleToDerived A' (DGBaseChange φ D)).map
          ((moduleExtension φ D).map (moduleCanonicalProjectiveResolution A D M).π) := rfl

lemma derivedExtensionAugmentation_isIso_of_objectwiseKFlat (M : ModuleCategory A D)
    (hD : localHomKFlat A D)
    (hM : moduleObjectwiseKFlat A D (ForgetEnrichment.to (Complex A) M)) :
    IsIso ((derivedExtensionAugmentation φ D).app M) := by
  have hP := moduleSemifree_objectwiseKFlat A D hD
    (moduleResolutionCandidate_semifree A D M)
  have hπ := moduleExtension_quasiIso_of_objectwiseKFlat φ D hP hM
    (moduleCanonicalProjectiveResolution A D M).π
    (moduleCanonicalProjectiveResolution A D M).quasiIso
  have := moduleToDerived_inverts A' (DGBaseChange φ D) _ hπ
  rw [derivedExtensionAugmentation_app]
  infer_instance

end SerrePositivity.DifferentialGraded.ScalarExtension
end

end ScalarExtensionNaturality

/-! ## ScalarExtensionComplexNaturality（旧 SerrePositivity/DifferentialGraded/Derived/ScalarExtensionComplexNaturality.lean） -/

/-! # 非有界複体の underived 比較自然変換 -/

@[expose] public section ScalarExtensionComplexNaturality
universe u w w'

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]
variable [HasDerivedCategory.{w'} (ModuleCat.{u} A')]

omit φ [HasDerivedCategory (ModuleCat.{u} A')] in
def ringDerivedInverseComparison :
    DerivedCategory.Q ⋙ (ringDerivedEquivalence A).inverse ≅
      (ringModuleEquivalence A).inverse ⋙ moduleToDerived A PUnit.{1} :=
  Functor.isoWhiskerRight (ringModuleEquivalence A).counitIso.symm
      (DerivedCategory.Q ⋙ (ringDerivedEquivalence A).inverse) ≪≫
    Functor.isoWhiskerLeft (ringModuleEquivalence A).inverse
      (Functor.isoWhiskerRight (ringDerivedEquivalence_fac A).symm
        (ringDerivedEquivalence A).inverse) ≪≫
    Functor.isoWhiskerLeft ((ringModuleEquivalence A).inverse ⋙ moduleToDerived A PUnit.{1})
      (ringDerivedEquivalence A).unitIso.symm

/-- 複体の主導来係数拡大から underived 係数拡大への自然変換。 -/
def complexDerivedExtensionAugmentation :
    DerivedCategory.Q ⋙ complexDerivedExtension φ ⟶ extension φ ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (ringDerivedInverseComparison (A := A)).hom
      (derivedExtension φ PUnit.{1} ⋙
        moduleDerivedEvaluation A' (DGBaseChange φ PUnit.{1}) PUnit.unit) ≫
    Functor.whiskerLeft (ringModuleEquivalence A).inverse
      (Functor.whiskerRight (derivedExtensionAugmentation φ PUnit.{1})
        (moduleDerivedEvaluation A' (DGBaseChange φ PUnit.{1}) PUnit.unit)) ≫
    (Functor.isoWhiskerLeft ((ringModuleEquivalence A).inverse ⋙ moduleExtension φ PUnit.{1})
      (eqToIso (moduleDerivedEvaluation_fac A' (DGBaseChange φ PUnit.{1}) PUnit.unit))).hom ≫
    (Functor.isoWhiskerLeft (ringModuleEquivalence A).inverse
      (Functor.isoWhiskerRight (moduleExtensionEvaluationIso φ PUnit.{1} PUnit.unit)
        DerivedCategory.Q)).hom ≫
    (Functor.isoWhiskerRight (ringModuleEquivalence A).counitIso
      (extension φ ⋙ DerivedCategory.Q)).hom

lemma complexDerivedExtensionAugmentation_isIso (K : Complex A) (hK : complexKFlat A K) :
    IsIso ((complexDerivedExtensionAugmentation φ).app K) := by
  let M := (ringModuleEquivalence A).inverse.obj K
  have hM : moduleObjectwiseKFlat A PUnit.{1} (ForgetEnrichment.to (Complex A) M) := by
    intro x
    cases x
    exact complexKFlat_of_iso A ((ringModuleEquivalence A).counitIso.app K) hK
  have := derivedExtensionAugmentation_isIso_of_objectwiseKFlat φ PUnit.{1} M
    (fun _ _ => complexKFlat_unit A) hM
  dsimp only [complexDerivedExtensionAugmentation, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  infer_instance

/-- K-flat な複体上で自然な underived 計算同型。 -/
def complexDerivedExtensionKFlatIso (K : Complex A) (hK : complexKFlat A K) :
    (complexDerivedExtension φ).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((extension φ).obj K) := by
  have := complexDerivedExtensionAugmentation_isIso φ K hK
  exact asIso ((complexDerivedExtensionAugmentation φ).app K)

lemma complexDerivedExtensionKFlatIso_naturality {K L : Complex A}
    (hK : complexKFlat A K) (hL : complexKFlat A L) (f : K ⟶ L) :
    (complexDerivedExtension φ).map (DerivedCategory.Q.map f) ≫
        (complexDerivedExtensionKFlatIso φ L hL).hom =
      (complexDerivedExtensionKFlatIso φ K hK).hom ≫
        DerivedCategory.Q.map ((extension φ).map f) :=
  (complexDerivedExtensionAugmentation φ).naturality f

end SerrePositivity.DifferentialGraded.ScalarExtension
end

end ScalarExtensionComplexNaturality

/-! ## ScalarExtensionTensor（旧 SerrePositivity/DifferentialGraded/Derived/ScalarExtensionTensor.lean） -/

/-! # K-flat 計算モデルによる導来 tensor の係数変更

選んだ右射影解像度 P について、P ⊗ N の A 上 K-flat 性と、
係数変更した P の相対 K-flat 性を明示的に受け取る。
これらを A′ の A-flat 性や任意の dg 圏に対する自動的な性質に置き換えない。
-/

@[expose] public section ScalarExtensionTensor
universe u v w w'

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory HomologicalComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

section
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

omit φ in
/-- 相対 K-flat な右加群では導来 tensor を underived に計算する。 -/
def relativeKFlatTensorComputation (M : ModuleCategory A D)
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M))
    (N : LeftModule A D) :
    (moduleDerivedTensorRight A D N).obj ((moduleToDerived A D).obj M) ≅
      DerivedCategory.Q.obj (BalancedTensor.obj A D (ForgetEnrichment.to (Complex A) M) N) := by
  let P := moduleCanonicalProjectiveResolution A D M
  have hP : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) P.obj) :=
    moduleSemifree_relativeKFlat A D (moduleResolutionCandidate_semifree A D M)
  have : QuasiIso ((BalancedTensor.rightTensorFunctor A D N).map P.π) :=
    BalancedTensor.rightTensor_relativeKFlat_quasiIso A D N hP hM P.π P.quasiIso
  exact moduleResolutionDerivedTensorComputation A D
    (moduleCanonicalProjectiveResolution A D) N M ≪≫
      asIso (DerivedCategory.Q.map ((BalancedTensor.rightTensorFunctor A D N).map P.π))

end

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]
variable [HasDerivedCategory.{w'} (ModuleCat.{u} A')]

/-- 導来係数変更と相対 tensor の比較。
左因子 N は、明示した K-flat 計算条件を満たす選択済みモデルとして扱う。 -/
def derivedTensorBaseChange {M : ModuleCategory A D}
    (P : ModuleProjectiveResolution A D M) (N : LeftModule A D)
    (hPN : complexKFlat A (BalancedTensor.obj A D (ForgetEnrichment.to (Complex A) P.obj) N))
    (hP' : moduleRelativeKFlat A' (DGBaseChange φ D)
      (rightModule φ D (ForgetEnrichment.to (Complex A) P.obj))) :
    (complexDerivedExtension φ).obj
        ((moduleDerivedTensorRight A D N).obj ((moduleToDerived A D).obj M)) ≅
      (moduleDerivedTensorRight A' (DGBaseChange φ D) (leftModule φ D N)).obj
        ((derivedExtension φ D).obj ((moduleToDerived A D).obj M)) :=
  (complexDerivedExtension φ).mapIso (moduleDerivedTensorRightResolutionComputation A D P N) ≪≫
    complexDerivedExtensionKFlatIso φ _ hPN ≪≫
    DerivedCategory.Q.mapIso (balancedIso φ D (ForgetEnrichment.to (Complex A) P.obj) N) ≪≫
    (relativeKFlatTensorComputation (DGBaseChange φ D) ((moduleExtension φ D).obj P.obj)
      hP' (leftModule φ D N)).symm ≪≫
    (moduleDerivedTensorRight A' (DGBaseChange φ D) (leftModule φ D N)).mapIso
      (derivedExtensionResolutionComputation φ D P).symm

omit [HasDerivedCategory (ModuleCat.{u} A)] in
/-- 係数変更後の coend 計算も両変数の全 dg 自然な射に自然。 -/
lemma derivedBalancedIso_naturality {M M' : ModuleCategory A D}
    {N N' : LeftModuleCategory A D} (f : M ⟶ M') (g : N ⟶ N') :
    DerivedCategory.Q.map ((extension φ).map (BalancedTensor.map A D f g)) ≫
        (DerivedCategory.Q.mapIso (balancedIso φ D
          (ForgetEnrichment.to (Complex A) M') (ForgetEnrichment.to (Complex A) N'))).hom =
      (DerivedCategory.Q.mapIso (balancedIso φ D
        (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N))).hom ≫
          DerivedCategory.Q.map (BalancedTensor.map A' (DGBaseChange φ D)
            ((moduleExtension φ D).map f) ((leftModuleExtension φ D).map g)) := by
  simp only [Functor.mapIso_hom, ← CategoryTheory.Functor.map_comp]
  exact congrArg DerivedCategory.Q.map (balancedIso_module_naturality φ D f g)

end SerrePositivity.DifferentialGraded.ScalarExtension
end

end ScalarExtensionTensor

/-! ## ScalarExtensionTensorCoherence（旧 SerrePositivity/DifferentialGraded/Derived/ScalarExtensionTensorCoherence.lean） -/

/-! # 導来係数変更と coend 計算モデルの自然性・単位・結合

一般のモデルでは比較射、A-K-flat な coend では比較同型となる。
-/

@[expose] public section ScalarExtensionTensorCoherence
universe u v w w'

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]
variable [HasDerivedCategory.{w'} (ModuleCat.{u} A')]

/-- 選んだ coend モデルの導来係数変更比較。 -/
def derivedBalancedComparison (M : RightModule A D) (N : LeftModule A D) :
    (complexDerivedExtension φ).obj (DerivedCategory.Q.obj (BalancedTensor.obj A D M N)) ⟶
      DerivedCategory.Q.obj (BalancedTensor.obj A' (DGBaseChange φ D)
        (rightModule φ D M) (leftModule φ D N)) :=
  (complexDerivedExtensionAugmentation φ).app (BalancedTensor.obj A D M N) ≫
    DerivedCategory.Q.map (balancedIso φ D M N).hom

lemma derivedBalancedComparison_isIso (M : RightModule A D) (N : LeftModule A D)
    (hMN : complexKFlat A (BalancedTensor.obj A D M N)) :
    IsIso (derivedBalancedComparison φ D M N) := by
  have := complexDerivedExtensionAugmentation_isIso φ _ hMN
  unfold derivedBalancedComparison
  infer_instance

lemma derivedBalancedComparison_naturality {M M' : ModuleCategory A D}
    {N N' : LeftModuleCategory A D} (f : M ⟶ M') (g : N ⟶ N') :
    (complexDerivedExtension φ).map (DerivedCategory.Q.map (BalancedTensor.map A D f g)) ≫
        derivedBalancedComparison φ D (ForgetEnrichment.to (Complex A) M')
          (ForgetEnrichment.to (Complex A) N') =
      derivedBalancedComparison φ D (ForgetEnrichment.to (Complex A) M)
        (ForgetEnrichment.to (Complex A) N) ≫
          DerivedCategory.Q.map (BalancedTensor.map A' (DGBaseChange φ D)
            ((moduleExtension φ D).map f) ((leftModuleExtension φ D).map g)) := by
  unfold derivedBalancedComparison
  have hn := (complexDerivedExtensionAugmentation φ).naturality (BalancedTensor.map A D f g)
  simp only [Functor.comp_map] at hn
  rw [← Category.assoc]
  erw [hn]
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp]
  erw [balancedIso_module_naturality φ D f g]
  rw [CategoryTheory.Functor.map_comp, Category.assoc]

/-- 右 representable の評価単位との可換図式。 -/
lemma derivedBalancedComparison_yoneda (z : D) (N : LeftModule A D) :
    derivedBalancedComparison φ D (representable A z) N ≫
        DerivedCategory.Q.map (yonedaBaseChangeIso φ D z N).hom =
      (complexDerivedExtension φ).map (DerivedCategory.Q.map
        (BalancedTensor.yonedaIso A D z N).hom) ≫
          (complexDerivedExtensionAugmentation φ).app (N.obj z) := by
  unfold derivedBalancedComparison
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, yonedaBaseChange_comparison]
  exact ((complexDerivedExtensionAugmentation φ).naturality
    (BalancedTensor.yonedaIso A D z N).hom).symm

/-- 左 representable の評価単位との可換図式。 -/
lemma derivedBalancedComparison_leftYoneda (z : D) (M : RightModule A D) :
    derivedBalancedComparison φ D M (leftRepresentable A z) ≫
        DerivedCategory.Q.map (leftYonedaBaseChangeIso φ D z M).hom =
      (complexDerivedExtension φ).map (DerivedCategory.Q.map
        (BalancedTensor.leftYonedaIso A D z M).hom) ≫
          (complexDerivedExtensionAugmentation φ).app (M.obj (Opposite.op z)) := by
  unfold derivedBalancedComparison
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, leftYonedaBaseChange_comparison]
  exact ((complexDerivedExtensionAugmentation φ).naturality
    (BalancedTensor.leftYonedaIso A D z M).hom).symm

/-- 複体パラメータの結合比較との可換図式。 -/
lemma derivedBalancedComparison_tensorModule (K : Complex A)
    (M : RightModule A D) (N : LeftModule A D) :
    derivedBalancedComparison φ D (tensorModule K M) N ≫
        DerivedCategory.Q.map (tensorModuleBaseChangeIso φ D K M N).hom =
      (complexDerivedExtension φ).map (DerivedCategory.Q.map
        (BalancedTensor.tensorModuleIso A D K M N).hom) ≫
          (complexDerivedExtensionAugmentation φ).app (K ⊗ BalancedTensor.obj A D M N) ≫
            DerivedCategory.Q.map ((tensorIso φ K (BalancedTensor.obj A D M N)).hom ≫
              (extension φ).obj K ◁ (balancedIso φ D M N).hom) := by
  unfold derivedBalancedComparison
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, tensorModuleBaseChange_comparison,
    CategoryTheory.Functor.map_comp, ← Category.assoc]
  have hn := (complexDerivedExtensionAugmentation φ).naturality
    (BalancedTensor.tensorModuleIso A D K M N).hom
  simp only [Functor.comp_map] at hn
  rw [← hn, Category.assoc]

end SerrePositivity.DifferentialGraded.ScalarExtension
end

end ScalarExtensionTensorCoherence
