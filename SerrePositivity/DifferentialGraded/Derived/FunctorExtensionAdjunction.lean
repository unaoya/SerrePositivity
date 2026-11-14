module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.DifferentialGraded.Tensor.LeftUnitRestriction
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddle.ModelIndependence
public import SerrePositivity.DifferentialGraded.Derived.BimoduleComposition.Resolution
public import SerrePositivity.DifferentialGraded.Module.Functor
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction
public import SerrePositivity.DifferentialGraded.Functor.ModuleValued
public import SerrePositivity.DifferentialGraded.Endomorphism.Derived.Adjunction
public import SerrePositivity.DifferentialGraded.Derived.Functor
public import SerrePositivity.DifferentialGraded.Derived.Projective
public import SerrePositivity.DifferentialGraded.Endomorphism.Basic
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddle.IteratedModels
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Additive
public import SerrePositivity.DifferentialGraded.Perfect.Basic
public import SerrePositivity.DifferentialGraded.Perfect.Compact.FiniteGeneration
public import SerrePositivity.DifferentialGraded.Endomorphism.Scalar.HomComparison
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import SerrePositivity.DifferentialGraded.Perfect.Compact.Enhancement
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.KFlatness
public import SerrePositivity.DifferentialGraded.Tensor.Associator.Pentagon
public import SerrePositivity.DifferentialGraded.Functor.Closed
public import SerrePositivity.DifferentialGraded.Functor.ModuleShift

/-!
# Derived.FunctorExtensionAdjunction

## 概要
15 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## LeftUnitRestrictionModel（旧 SerrePositivity/DifferentialGraded/Derived/LeftUnitRestrictionModel.lean） -/

/-! # 制限後の任意K-flat解像度で計算する左単位square

## 概要
制限後の任意K-flat解像度で計算する左単位square。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section LeftUnitRestrictionModel
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C] (F : DGFunctor A D B)
  (P : BimoduleCategory A B C)

local notation "RP" => Functor.obj
  (BimoduleCategory.middleRightRestrictionFunctor A B D C F) P
local notation "LD" => Functor.obj (BimoduleCategory.middleLeftRestrictionFunctor A B B D F)
  (BimoduleCategory.of A B B (Bimodule.diagonal A B))
local notation "DD" => BimoduleCategory.of A D D (Bimodule.diagonal A D)
local notation "qD" => Bimodule.diagonalRestrictionMap A D B F

omit [Small.{u} C] in
/-- 指定増大射付き左単位squareを、既存の導来局所化に送る。 -/
lemma leftUnitRestriction_localized_augmentation (R : BimoduleCategory A D C) (q : R ⟶ RP) :
    (bimoduleToDerived A D C).map (composeMap A D D C qD (𝟙 R)) ≫
      (bimoduleToDerived A D C).map (composeRightRestrictionIso A B D D C F LD R).hom ≫
      (bimoduleToDerived A D C).map
        ((BimoduleCategory.middleRightRestrictionFunctor A B D C F).map
          (middleRestrictionResolvedMap A B B D C F
            (BimoduleCategory.of A B B (Bimodule.diagonal A B)) P R q)) ≫
      (bimoduleToDerived A D C).map
        ((BimoduleCategory.middleRightRestrictionFunctor A B D C F).map
          (leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom) =
    (bimoduleToDerived A D C).map
        (leftBimoduleUnitIso A D C (BimoduleCategory.underlying A D C R)).hom ≫
      (bimoduleToDerived A D C).map q := by
  have h := congrArg ((bimoduleToDerived A D C).map)
    (leftUnitRestriction_augmentation A B D C F P R q)
  simpa only [middleRestrictionResolvedMap, BimoduleCategory.middleLeftRestrictionFunctor,
    BimoduleCategory.underlying, BimoduleCategory.of,
    CategoryTheory.Functor.map_comp, Category.assoc] using h

/-- 任意の指定K-flat解像度による計算経路は、既存の導来左単位子そのもの。 -/
lemma derivedLeftUnitRestriction_resolution (hC : localHomKFlat A C)
    (R : RightKFlatBimoduleCategory A D C) (q : R.obj ⟶ RP)
    (hq : BimoduleCategory.quasiIso A D C q) :
    (derivedBimoduleComposeResolutionComputation A D D C hC RP R q hq).hom.app
        ((bimoduleToDerived A D D).obj DD) ≫
      (bimoduleToDerived A D C).map (composeMap A D D C qD (𝟙 R.obj)) ≫
      (bimoduleToDerived A D C).map (composeRightRestrictionIso A B D D C F LD R.obj).hom ≫
      (bimoduleToDerived A D C).map
        ((BimoduleCategory.middleRightRestrictionFunctor A B D C F).map
          (middleRestrictionResolvedMap A B B D C F
            (BimoduleCategory.of A B B (Bimodule.diagonal A B)) P R.obj q)) ≫
      (bimoduleToDerived A D C).map
        ((BimoduleCategory.middleRightRestrictionFunctor A B D C F).map
          (leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom) =
    (derivedBimoduleLeftUnitIso A D C hC).hom.app ((bimoduleToDerived A D C).obj RP) := by
  rw [leftUnitRestriction_localized_augmentation A B D C F P R.obj q,
    derivedBimoduleLeftUnitIso_resolution_app A D C hC RP R q hq]
  rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end LeftUnitRestrictionModel

/-! ## FunctorExtensionProjective（旧 SerrePositivity/DifferentialGraded/Derived/FunctorExtensionProjective.lean） -/

/-! # graph延長の主K随伴とホモトピー射影性の保存

## 概要
graph延長の主K随伴とホモトピー射影性の保存。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section FunctorExtensionProjective
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- 制限の全Homモデルを使った、既存の閉零随伴。 -/
def dgModuleEnrichedRestrictionAdjunction :
    (dgModuleExtension A D E F).onClosed ⊣ (dgModuleRestriction A D E F.op).onClosed :=
  (dgModuleExtensionRestrictionAdjunction A D E F).ofNatIsoRight
    (eqToIso (dgModuleRestriction_onClosed_eq A D E F.op)).symm

/-- 主ホモトピー圏上でのgraph延長–制限随伴。 -/
def dgModuleHomotopyAdjunction :
    (dgModuleExtension A D E F).onHomotopy ⊣ (dgModuleRestriction A D E F.op).onHomotopy :=
  DGFunctor.homotopyAdjunction _ _ (dgModuleEnrichedRestrictionAdjunction A D E F)

lemma dgModuleHomotopyRestriction_quasiIso
    {M N : ModuleHomotopyCategory A E} (f : M ⟶ N)
    (hf : moduleHomotopyQuasiIso A E f) :
    moduleHomotopyQuasiIso A D ((dgModuleRestriction A D E F.op).onHomotopy.map f) := by
  obtain ⟨M⟩ := M
  obtain ⟨N⟩ := N
  obtain ⟨g, rfl⟩ := (moduleToHomotopy A E).map_surjective f
  change moduleHomotopyQuasiIso A D ((moduleToHomotopy A D).map
    ((dgModuleRestriction A D E F.op).onClosed.map g))
  rw [dgModuleRestriction_map]
  exact (moduleHomotopyQuasiIso_map_iff A D _).mpr
    (moduleRestriction_quasiIso A D E F.op g ((moduleHomotopyQuasiIso_map_iff A E g).mp hf))

/-- 任意のdg関手のgraph延長はホモトピー射影的右加群を保つ。 -/
lemma dgModuleExtension_homotopicallyProjective {P : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P) :
    moduleHomotopicallyProjective A E ((dgModuleExtension A D E F).onClosed.obj P) := by
  apply moduleHomotopicallyProjective_of_coyoneda_inverts A E
  intro X Y f hf
  apply (CategoryTheory.isIso_iff_bijective _).mpr
  let adj := dgModuleHomotopyAdjunction A D E F
  let Rf := (dgModuleRestriction A D E F.op).onHomotopy.map f
  have hRf := dgModuleHomotopyRestriction_quasiIso A D E F f hf
  have hpost := (CategoryTheory.isIso_iff_bijective _).mp
    (moduleHomotopicallyProjective_coyoneda_inverts A D hP Rf hRf)
  change Function.Bijective (fun s :
    (dgModuleExtension A D E F).onHomotopy.obj ((moduleToHomotopy A D).obj P) ⟶ X => s ≫ f)
  let eX := adj.homEquiv ((moduleToHomotopy A D).obj P) X
  let eY := adj.homEquiv ((moduleToHomotopy A D).obj P) Y
  have heq : (fun s :
      (dgModuleExtension A D E F).onHomotopy.obj ((moduleToHomotopy A D).obj P) ⟶ X => s ≫ f) =
    fun s => eY.symm (eX s ≫ Rf) := by
    funext s
    apply eY.injective
    rw [Equiv.apply_symm_apply]
    exact adj.homEquiv_naturality_right s f
  rw [heq]
  exact eY.symm.bijective.comp (hpost.comp eX.bijective)

end SerrePositivity.DifferentialGraded
end

end FunctorExtensionProjective

/-! ## FunctorExtensionHom（旧 SerrePositivity/DifferentialGraded/Derived/FunctorExtensionHom.lean） -/

/-! # graph導来延長と導来制限の射集合の同値

## 概要
graph導来延長と導来制限の射集合の同値。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section FunctorExtensionHom
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- 実際の加群の導来制限の計算同型。 -/
def dgDerivedRestrictionComputation (M : ModuleCategory A E) :
    (dgDerivedRestriction A D E F).obj ((moduleToDerived A E).obj M) ≅
      (moduleToDerived A D).obj ((dgModuleRestriction A D E F.op).onClosed.obj M) :=
  eqToIso (congrArg (fun G => G.obj M) (dgDerivedRestriction_fac A D E F))

/-- 射影的始域に対する、graph導来延長–制限のHom同値。 -/
def dgProjectiveDerivedExtensionHomEquiv (P : ModuleCategory A D)
    (hP : moduleHomotopicallyProjective A D P) (M : ModuleCategory A E) :
    ((moduleToDerived A E).obj ((dgModuleExtension A D E F).onClosed.obj P) ⟶
        (moduleToDerived A E).obj M) ≃
      ((moduleToDerived A D).obj P ⟶
        (dgDerivedRestriction A D E F).obj ((moduleToDerived A E).obj M)) :=
  (moduleProjectiveDerivedHomEquiv A E
    (dgModuleExtension_homotopicallyProjective A D E F hP) M).symm.trans
    (((dgModuleHomotopyAdjunction A D E F).homEquiv
      ((moduleToHomotopy A D).obj P) ((moduleToHomotopy A E).obj M)).trans
      ((moduleProjectiveDerivedHomEquiv A D hP
        ((dgModuleRestriction A D E F.op).onClosed.obj M)).trans
          (Iso.homCongr (Iso.refl _) (dgDerivedRestrictionComputation A D E F M).symm)))

/-- 指定された実際の加群の導来像に対するHom同値。自然性は別途検証する。 -/
def dgDerivedExtensionHomEquivOnModules (N : ModuleCategory A D) (M : ModuleCategory A E) :
    ((dgDerivedExtension A D E F).obj ((moduleToDerived A D).obj N) ⟶
        (moduleToDerived A E).obj M) ≃
      ((moduleToDerived A D).obj N ⟶
        (dgDerivedRestriction A D E F).obj ((moduleToDerived A E).obj M)) := by
  let P := moduleCanonicalProjectiveResolution A D N
  exact (Iso.homCongr (dgDerivedExtensionResolutionComputation A D E F P) (Iso.refl _)).trans
    ((dgProjectiveDerivedExtensionHomEquiv A D E F P.obj P.projective M).trans
      (Iso.homCongr (moduleDerivedIso A D P.π P.quasiIso) (Iso.refl _)))

/-- 主導来圏の任意の対象の射集合同値。 -/
def dgDerivedExtensionHomEquiv (X : DerivedModuleCategory A D) (Y : DerivedModuleCategory A E) :
    ((dgDerivedExtension A D E F).obj X ⟶ Y) ≃
      (X ⟶ (dgDerivedRestriction A D E F).obj Y) :=
  dgDerivedExtensionHomEquivOnModules A D E F X.as.obj Y.as.obj

end SerrePositivity.DifferentialGraded
end

end FunctorExtensionHom

/-! ## FunctorExtensionProjectiveNaturality（旧 SerrePositivity/DifferentialGraded/Derived/FunctorExtensionProjectiveNaturality.lean） -/

/-! # 射影的始域でのgraph導来延長Hom同値の自然性

## 概要
射影的始域でのgraph導来延長Hom同値の自然性。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section FunctorExtensionProjectiveNaturality
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

lemma dgProjectiveDerivedExtensionHomEquiv_map (P : ModuleCategory A D)
    (hP : moduleHomotopicallyProjective A D P) (M : ModuleCategory A E)
    (s : (dgModuleExtension A D E F).onClosed.obj P ⟶ M) :
    dgProjectiveDerivedExtensionHomEquiv A D E F P hP M ((moduleToDerived A E).map s) =
      (moduleToDerived A D).map
          ((dgModuleEnrichedRestrictionAdjunction A D E F).homEquiv P M s) ≫
        (dgDerivedRestrictionComputation A D E F M).inv := by
  have hs := moduleProjectiveDerivedHomEquiv_map A E
    (dgModuleExtension_homotopicallyProjective A D E F hP) s
  unfold dgProjectiveDerivedExtensionHomEquiv
  simp only [Equiv.trans_apply]
  rw [← hs, Equiv.symm_apply_apply]
  have ht := DGFunctor.homotopyAdjunction_homEquiv_map
    (dgModuleExtension A D E F) (dgModuleRestriction A D E F.op)
    (dgModuleEnrichedRestrictionAdjunction A D E F) P M s
  have hu := congrArg (moduleProjectiveDerivedHomEquiv A D hP
    ((dgModuleRestriction A D E F.op).onClosed.obj M)) ht
  have hv := hu.trans (moduleProjectiveDerivedHomEquiv_map A D hP
    ((dgModuleEnrichedRestrictionAdjunction A D E F).homEquiv P M s))
  exact (congrArg (Iso.homCongr (Iso.refl _)
    (dgDerivedRestrictionComputation A D E F M).symm) hv).trans (by simp [Iso.homCongr])

lemma dgDerivedRestrictionComputation_inv_naturality {M M' : ModuleCategory A E} (f : M ⟶ M') :
    (moduleToDerived A D).map ((dgModuleRestriction A D E F.op).onClosed.map f) ≫
        (dgDerivedRestrictionComputation A D E F M').inv =
      (dgDerivedRestrictionComputation A D E F M).inv ≫
        (dgDerivedRestriction A D E F).map ((moduleToDerived A E).map f) := by
  have h := (eqToIso (dgDerivedRestriction_fac A D E F)).inv.naturality f
  rw [dgModuleRestriction_map]
  exact h

lemma dgProjectiveDerivedExtensionHomEquiv_naturality_right
    (P : ModuleCategory A D) (hP : moduleHomotopicallyProjective A D P)
    {M M' : ModuleCategory A E}
    (φ : (moduleToDerived A E).obj ((dgModuleExtension A D E F).onClosed.obj P) ⟶
      (moduleToDerived A E).obj M) (f : M ⟶ M') :
    dgProjectiveDerivedExtensionHomEquiv A D E F P hP M'
        (φ ≫ (moduleToDerived A E).map f) =
      dgProjectiveDerivedExtensionHomEquiv A D E F P hP M φ ≫
        (dgDerivedRestriction A D E F).map ((moduleToDerived A E).map f) := by
  obtain ⟨s, rfl⟩ := moduleProjectiveToDerived_map_surjective A E
    (dgModuleExtension_homotopicallyProjective A D E F hP) φ
  rw [← Functor.map_comp, dgProjectiveDerivedExtensionHomEquiv_map,
    dgProjectiveDerivedExtensionHomEquiv_map, Adjunction.homEquiv_naturality_right,
    Functor.map_comp, Category.assoc, dgDerivedRestrictionComputation_inv_naturality,
    Category.assoc]

lemma dgProjectiveDerivedExtensionHomEquiv_naturality_left
    (P Q : ModuleCategory A D) (hP : moduleHomotopicallyProjective A D P)
    (hQ : moduleHomotopicallyProjective A D Q) (M : ModuleCategory A E) (f : P ⟶ Q)
    (φ : (moduleToDerived A E).obj ((dgModuleExtension A D E F).onClosed.obj Q) ⟶
      (moduleToDerived A E).obj M) :
    dgProjectiveDerivedExtensionHomEquiv A D E F P hP M
        ((moduleToDerived A E).map ((dgModuleExtension A D E F).onClosed.map f) ≫ φ) =
      (moduleToDerived A D).map f ≫ dgProjectiveDerivedExtensionHomEquiv A D E F Q hQ M φ := by
  obtain ⟨s, rfl⟩ := moduleProjectiveToDerived_map_surjective A E
    (dgModuleExtension_homotopicallyProjective A D E F hQ) φ
  rw [← Functor.map_comp, dgProjectiveDerivedExtensionHomEquiv_map,
    dgProjectiveDerivedExtensionHomEquiv_map, Adjunction.homEquiv_naturality_left,
    Functor.map_comp, Category.assoc]

end SerrePositivity.DifferentialGraded
end

end FunctorExtensionProjectiveNaturality

/-! ## FunctorExtensionHomNaturality（旧 SerrePositivity/DifferentialGraded/Derived/FunctorExtensionHomNaturality.lean） -/

/-! # graph導来延長Hom同値の実際の加群射に対する自然性

## 概要
graph導来延長Hom同値の実際の加群射に対する自然性。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section FunctorExtensionHomNaturality
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

lemma dgDerivedExtensionHomEquivOnModules_apply
    (N : ModuleCategory A D) (M : ModuleCategory A E)
    (φ : (dgDerivedExtension A D E F).obj
        ((moduleToDerived A D).obj N) ⟶ (moduleToDerived A E).obj M) :
    dgDerivedExtensionHomEquivOnModules A D E F N M φ =
      (moduleDerivedIso A D
          (moduleCanonicalProjectiveResolution A D N).π
          (moduleCanonicalProjectiveResolution A D N).quasiIso).inv ≫
        dgProjectiveDerivedExtensionHomEquiv A D E F
          (moduleCanonicalProjectiveResolution A D N).obj
          (moduleCanonicalProjectiveResolution A D N).projective M
          ((dgDerivedExtensionResolutionComputation A D E F
            (moduleCanonicalProjectiveResolution A D N)).inv ≫ φ) := by
  simp [dgDerivedExtensionHomEquivOnModules, Iso.homCongr]

lemma dgDerivedExtensionHomEquivOnModules_naturality_right
    (N : ModuleCategory A D) {M M' : ModuleCategory A E}
    (φ : (dgDerivedExtension A D E F).obj
        ((moduleToDerived A D).obj N) ⟶ (moduleToDerived A E).obj M)
    (f : M ⟶ M') :
    dgDerivedExtensionHomEquivOnModules A D E F N M'
        (φ ≫ (moduleToDerived A E).map f) =
      dgDerivedExtensionHomEquivOnModules A D E F N M φ ≫
        (dgDerivedRestriction A D E F).map ((moduleToDerived A E).map f) := by
  rw [dgDerivedExtensionHomEquivOnModules_apply,
    dgDerivedExtensionHomEquivOnModules_apply, ← Category.assoc,
    dgProjectiveDerivedExtensionHomEquiv_naturality_right, Category.assoc]

lemma dgResolutionLift_derived_fac
    {N N' : ModuleCategory A D}
    (P : ModuleProjectiveResolution A D N)
    (Q : ModuleProjectiveResolution A D N') (f : N ⟶ N') :
    (moduleToDerived A D).map (P.lift Q f) ≫
        (moduleToDerived A D).map Q.π =
      (moduleToDerived A D).map P.π ≫
        (moduleToDerived A D).map f := by
  have h := P.lift_fac Q f
  rw [← Functor.map_comp, ← Functor.map_comp] at h
  have h' := moduleQuasiIso_equalizes_boundary A D
    (moduleToDerived A D)
    (moduleToDerived_inverts A D) _ _
    ((toHomotopy_map_eq_iff A (RightModule A D) _ _).mp h)
  simpa only [Functor.map_comp] using h'

lemma dgResolutionLift_derived_inv_naturality
    {N N' : ModuleCategory A D}
    (P : ModuleProjectiveResolution A D N)
    (Q : ModuleProjectiveResolution A D N') (f : N ⟶ N') :
    (moduleDerivedIso A D P.π P.quasiIso).inv ≫
        (moduleToDerived A D).map (P.lift Q f) =
      (moduleToDerived A D).map f ≫
        (moduleDerivedIso A D Q.π Q.quasiIso).inv := by
  apply (cancel_mono (moduleDerivedIso A D Q.π Q.quasiIso).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change (moduleDerivedIso A D P.π P.quasiIso).inv ≫
    (moduleToDerived A D).map (P.lift Q f) ≫
      (moduleToDerived A D).map Q.π = _
  rw [dgResolutionLift_derived_fac]
  exact Iso.inv_hom_id_assoc _ _

lemma dgDerivedExtensionHomEquivOnModules_naturality_left
    {N N' : ModuleCategory A D} (M : ModuleCategory A E)
    (f : N ⟶ N')
    (φ : (dgDerivedExtension A D E F).obj
        ((moduleToDerived A D).obj N') ⟶ (moduleToDerived A E).obj M) :
    dgDerivedExtensionHomEquivOnModules A D E F N M
        ((dgDerivedExtension A D E F).map
          ((moduleToDerived A D).map f) ≫ φ) =
      (moduleToDerived A D).map f ≫
        dgDerivedExtensionHomEquivOnModules A D E F N' M φ := by
  rw [dgDerivedExtensionHomEquivOnModules_apply,
    dgDerivedExtensionHomEquivOnModules_apply, ← Category.assoc,
    dgDerivedExtensionResolutionComputation_inv_naturality, Category.assoc,
    dgProjectiveDerivedExtensionHomEquiv_naturality_left, ← Category.assoc,
    dgResolutionLift_derived_inv_naturality, Category.assoc]

end SerrePositivity.DifferentialGraded
end

end FunctorExtensionHomNaturality

/-! ## FunctorExtensionAdjunction（旧 SerrePositivity/DifferentialGraded/Derived/FunctorExtensionAdjunction.lean） -/

/-! # graph導来延長と導来制限の随伴

## 概要
graph導来延長と導来制限の随伴。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section FunctorExtensionAdjunction
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

lemma dgDerivedExtensionHomEquiv_naturality_right (X : DerivedModuleCategory A D)
    {Y Y' : DerivedModuleCategory A E}
    (φ : (dgDerivedExtension A D E F).obj X ⟶ Y) (g : Y ⟶ Y') :
    dgDerivedExtensionHomEquiv A D E F X Y' (φ ≫ g) =
      dgDerivedExtensionHomEquiv A D E F X Y φ ≫ (dgDerivedRestriction A D E F).map g := by
  apply localizationHom_naturality_right (moduleQuasiIso A E)
    (dgDerivedExtension A D E F) (dgDerivedRestriction A D E F)
    (fun X Y φ => dgDerivedExtensionHomEquiv A D E F X Y φ)
  intro X M M' f φ
  exact dgDerivedExtensionHomEquivOnModules_naturality_right A D E F X.as.obj φ f

lemma dgDerivedExtensionHomEquiv_naturality_left {X X' : DerivedModuleCategory A D}
    (f : X ⟶ X') (Y : DerivedModuleCategory A E)
    (φ : (dgDerivedExtension A D E F).obj X' ⟶ Y) :
    dgDerivedExtensionHomEquiv A D E F X Y ((dgDerivedExtension A D E F).map f ≫ φ) =
      f ≫ dgDerivedExtensionHomEquiv A D E F X' Y φ := by
  apply localizationHom_naturality_left (moduleQuasiIso A D)
    (dgDerivedExtension A D E F) (dgDerivedRestriction A D E F)
    (fun X Y φ => dgDerivedExtensionHomEquiv A D E F X Y φ)
  intro N N' f Y φ
  exact dgDerivedExtensionHomEquivOnModules_naturality_left A D E F Y.as.obj f φ

/-- 任意dg関手のgraph導来延長と導来制限は実際に随伴する。 -/
def dgDerivedExtensionRestrictionAdjunction :
    dgDerivedExtension A D E F ⊣ dgDerivedRestriction A D E F :=
  Adjunction.mkOfHomEquiv {
    homEquiv := dgDerivedExtensionHomEquiv A D E F
    homEquiv_naturality_right := fun φ g =>
      dgDerivedExtensionHomEquiv_naturality_right A D E F _ φ g
    homEquiv_naturality_left_symm := by
      intro X X' Y f g
      apply (dgDerivedExtensionHomEquiv A D E F X Y).injective
      rw [Equiv.apply_symm_apply, dgDerivedExtensionHomEquiv_naturality_left,
        Equiv.apply_symm_apply] }

/-- 射影解像度で構成した主導来延長–制限随伴の単位。 -/
def dgDerivedExtensionUnit : 𝟭 (DerivedModuleCategory A D) ⟶
    dgDerivedExtension A D E F ⋙ dgDerivedRestriction A D E F :=
  (dgDerivedExtensionRestrictionAdjunction A D E F).unit

/-- 射影解像度で構成した主導来延長–制限随伴の余単位。 -/
def dgDerivedExtensionCounit : dgDerivedRestriction A D E F ⋙
    dgDerivedExtension A D E F ⟶ 𝟭 (DerivedModuleCategory A E) :=
  (dgDerivedExtensionRestrictionAdjunction A D E F).counit

lemma dgDerivedExtension_left_triangle (X : DerivedModuleCategory A D) :
    (dgDerivedExtension A D E F).map ((dgDerivedExtensionUnit A D E F).app X) ≫
      (dgDerivedExtensionCounit A D E F).app ((dgDerivedExtension A D E F).obj X) = 𝟙 _ :=
  (dgDerivedExtensionRestrictionAdjunction A D E F).left_triangle_components X

lemma dgDerivedExtension_right_triangle (Y : DerivedModuleCategory A E) :
    (dgDerivedExtensionUnit A D E F).app ((dgDerivedRestriction A D E F).obj Y) ≫
      (dgDerivedRestriction A D E F).map ((dgDerivedExtensionCounit A D E F).app Y) = 𝟙 _ :=
  (dgDerivedExtensionRestrictionAdjunction A D E F).right_triangle_components Y

end SerrePositivity.DifferentialGraded
end

end FunctorExtensionAdjunction

/-! ## FunctorExtensionTriangles（旧 SerrePositivity/DifferentialGraded/Derived/FunctorExtensionTriangles.lean） -/

/-! # graph導来随伴に整合する整数shiftと三角性

## 概要
graph導来随伴に整合する整数shiftと三角性。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section FunctorExtensionTriangles
universe u v w

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

local instance : (dgDerivedRestriction A D E F).CommShift ℤ := dgDerivedRestrictionCommShift A D E F
local instance : (dgDerivedRestriction A D E F).IsTriangulated :=
  dgDerivedRestrictionIsTriangulated A D E F
local instance : (dgDerivedRestriction A D E F).Additive := dgDerivedRestriction_additive A D E F

/-- 実際の導来随伴から左関手へ運ぶ、随伴と整合するshift。 -/
@[instance_reducible]
def dgDerivedExtensionCommShift : (dgDerivedExtension A D E F).CommShift ℤ :=
  (dgDerivedExtensionRestrictionAdjunction A D E F).leftAdjointCommShift ℤ

lemma dgDerivedExtensionRestrictionAdjunction_commShift :
    letI := dgDerivedExtensionCommShift A D E F
    (dgDerivedExtensionRestrictionAdjunction A D E F).CommShift ℤ :=
  (dgDerivedExtensionRestrictionAdjunction A D E F).commShift_of_rightAdjoint ℤ

lemma dgDerivedExtensionUnit_commShift :
    letI := dgDerivedExtensionCommShift A D E F
    NatTrans.CommShift (dgDerivedExtensionUnit A D E F) ℤ := by
  let := dgDerivedExtensionCommShift A D E F
  let := dgDerivedExtensionRestrictionAdjunction_commShift A D E F
  unfold dgDerivedExtensionUnit
  infer_instance

lemma dgDerivedExtensionCounit_commShift :
    letI := dgDerivedExtensionCommShift A D E F
    NatTrans.CommShift (dgDerivedExtensionCounit A D E F) ℤ := by
  let := dgDerivedExtensionCommShift A D E F
  let := dgDerivedExtensionRestrictionAdjunction_commShift A D E F
  unfold dgDerivedExtensionCounit
  infer_instance

lemma dgDerivedExtensionIsTriangulated :
    letI := dgDerivedExtensionCommShift A D E F
    (dgDerivedExtension A D E F).IsTriangulated := by
  let := dgDerivedExtensionCommShift A D E F
  let := dgDerivedExtensionRestrictionAdjunction_commShift A D E F
  exact (dgDerivedExtensionRestrictionAdjunction A D E F).isTriangulated_leftAdjoint

lemma dgDerivedExtension_additive : (dgDerivedExtension A D E F).Additive :=
  (dgDerivedExtensionRestrictionAdjunction A D E F).left_adjoint_additive

end SerrePositivity.DifferentialGraded
end

end FunctorExtensionTriangles

/-! ## FunctorExtensionPerfect（旧 SerrePositivity/DifferentialGraded/Derived/FunctorExtensionPerfect.lean） -/

/-! # graph導来延長のperfect・compact対象の保存

## 概要
graph導来延長のperfect・compact対象の保存。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section FunctorExtensionPerfect
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)
local instance : (dgDerivedExtension A D E F).CommShift ℤ := dgDerivedExtensionCommShift A D E F
local instance : (dgDerivedExtension A D E F).IsTriangulated :=
  dgDerivedExtensionIsTriangulated A D E F

lemma dgDerivedExtension_perfect {X : DerivedModuleCategory A D} (hX : modulePerfect A D X) :
    modulePerfect A E ((dgDerivedExtension A D E F).obj X) := by
  let P := (modulePerfect A E).inverseImage (dgDerivedExtension A D E F)
  have : P.IsTriangulated := by dsimp [P]; infer_instance
  have : P.IsClosedUnderIsomorphisms := by dsimp [P]; infer_instance
  have : P.IsStableUnderRetracts :=
    ⟨fun r hY => (modulePerfect A E).prop_of_retract (r.map (dgDerivedExtension A D E F)) hY⟩
  apply ((modulePerfect_le_iff_generators A D P).2 ?_) X hX
  intro d
  exact (modulePerfect A E).prop_of_iso (dgDerivedExtensionRepresentableIso A D E F d).symm
    (modulePerfectOver_representable A E (F.obj d) (Set.mem_univ _))

/-- U13dのcompact⇒perfectを再利用する。追加のcompact生成入力は要らない。 -/
lemma dgDerivedExtension_compact {X : DerivedModuleCategory A D} (hX : moduleCompact A D X) :
    moduleCompact A E ((dgDerivedExtension A D E F).obj X) :=
  modulePerfect_compact A E (dgDerivedExtension_perfect A D E F (moduleCompact_perfect A D hX))

end SerrePositivity.DifferentialGraded
end

end FunctorExtensionPerfect

/-! ## FunctorExtensionUnitComputation（旧 SerrePositivity/DifferentialGraded/Derived/FunctorExtensionUnitComputation.lean） -/

/-! # 導来単位と射影解像度上の実際の単位の計算

## 概要
導来単位と射影解像度上の実際の単位の計算。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section FunctorExtensionUnitComputation
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

private lemma rightAdjointIso_unit {C : Type*} {T : Type*}
    [Category* C] [Category* T] {L : C ⥤ T} {R R' : T ⥤ C}
    (adj : L ⊣ R) (e : R ≅ R') (X : C) :
    (adj.ofNatIsoRight e).unit.app X = adj.unit.app X ≫ e.hom.app (L.obj X) := by
  rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.homEquiv_id]

private lemma functorEqIso_inv_app {C : Type*} {T : Type*}
    [Category* C] [Category* T] {G H : C ⥤ T} (h : G = H) (X : C) :
    (eqToIso h).inv.app X = (eqToIso (congrArg (fun J => J.obj X) h)).inv := by
  cases h
  rfl

lemma dgModuleExtensionRestrictionAdjunction_unit (M : ModuleCategory A D) :
    (dgModuleExtensionRestrictionAdjunction A D E F).unit.app M =
      functorExtensionUnit A D E F (ForgetEnrichment.to (Complex A) M) := rfl

lemma dgModuleEnrichedRestrictionAdjunction_unit (M : ModuleCategory A D) :
    (dgModuleEnrichedRestrictionAdjunction A D E F).unit.app M =
      functorExtensionUnit A D E F (ForgetEnrichment.to (Complex A) M) := by
  have h := rightAdjointIso_unit (dgModuleExtensionRestrictionAdjunction A D E F)
    (eqToIso (dgModuleRestriction_onClosed_eq A D E F.op)).symm M
  have hi : (eqToIso (dgModuleRestriction_onClosed_eq A D E F.op)).symm.hom.app
      ((dgModuleExtension A D E F).onClosed.obj M) = 𝟙 _ := by
    change (eqToIso (dgModuleRestriction_onClosed_eq A D E F.op)).inv.app
      ((dgModuleExtension A D E F).onClosed.obj M) = _
    rw [functorEqIso_inv_app]
    rfl
  refine h.trans ?_
  refine (congrArg (fun t => (dgModuleExtensionRestrictionAdjunction A D E F).unit.app M ≫ t)
    hi).trans ?_
  exact (Category.comp_id _).trans (dgModuleExtensionRestrictionAdjunction_unit A D E F M)

lemma dgDerivedExtensionRestrictionAdjunction_homEquiv :
    (dgDerivedExtensionRestrictionAdjunction A D E F).homEquiv =
      dgDerivedExtensionHomEquiv A D E F :=
  Adjunction.mkOfHomEquiv_homEquiv _

lemma dgDerivedExtensionUnit_computation (M : ModuleCategory A D) :
    (dgDerivedExtensionUnit A D E F).app ((moduleToDerived A D).obj M) ≫
      (dgDerivedRestriction A D E F).map
        (dgDerivedExtensionResolutionComputation A D E F
          (moduleCanonicalProjectiveResolution A D M)).hom =
    (moduleDerivedIso A D (moduleCanonicalProjectiveResolution A D M).π
      (moduleCanonicalProjectiveResolution A D M).quasiIso).inv ≫
      (moduleToDerived A D).map (functorExtensionUnit A D E F
        (ForgetEnrichment.to (Complex A) (moduleCanonicalProjectiveResolution A D M).obj)) ≫
      (dgDerivedRestrictionComputation A D E F
        ((dgModuleExtension A D E F).onClosed.obj
          (moduleCanonicalProjectiveResolution A D M).obj)).inv := by
  have h := (dgDerivedExtensionRestrictionAdjunction A D E F).homEquiv_unit
    ((moduleToDerived A D).obj M)
    ((moduleToDerived A E).obj ((dgModuleExtension A D E F).onClosed.obj
      (moduleCanonicalProjectiveResolution A D M).obj))
    (dgDerivedExtensionResolutionComputation A D E F
      (moduleCanonicalProjectiveResolution A D M)).hom
  refine h.symm.trans ?_
  rw [dgDerivedExtensionRestrictionAdjunction_homEquiv]
  change dgDerivedExtensionHomEquivOnModules A D E F M
    ((dgModuleExtension A D E F).onClosed.obj
      (moduleCanonicalProjectiveResolution A D M).obj)
    (dgDerivedExtensionResolutionComputation A D E F
      (moduleCanonicalProjectiveResolution A D M)).hom = _
  rw [dgDerivedExtensionHomEquivOnModules_apply, Iso.inv_hom_id]
  rw [← CategoryTheory.Functor.map_id (moduleToDerived A E)]
  rw [dgProjectiveDerivedExtensionHomEquiv_map, Adjunction.homEquiv_id,
    dgModuleEnrichedRestrictionAdjunction_unit]

end SerrePositivity.DifferentialGraded
end

end FunctorExtensionUnitComputation

/-! ## FunctorExtensionRepresentableUnit（旧 SerrePositivity/DifferentialGraded/Derived/FunctorExtensionRepresentableUnit.lean） -/

/-! # Hom準同型に沿う導来単位の代表加群上での可逆性

## 概要
Hom準同型に沿う導来単位の代表加群上での可逆性。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section FunctorExtensionRepresentableUnit
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

lemma functorExtensionUnit_resolution_quasiIso {M : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M)
    (hunit : moduleQuasiIso A D
      (functorExtensionUnit A D E F (ForgetEnrichment.to (Complex A) M)))
    (P : ModuleProjectiveResolution A D M) :
    moduleQuasiIso A D (functorExtensionUnit A D E F
      (ForgetEnrichment.to (Complex A) P.obj)) := by
  have hg := moduleRestriction_quasiIso A D E F.op _
    (dgModuleExtension_projective_quasiIso A D E F P.projective hM P.π P.quasiIso)
  have hn := (dgModuleUnit A D E F).naturality P.π
  change P.π ≫ functorExtensionUnit A D E F (ForgetEnrichment.to (Complex A) M) =
    functorExtensionUnit A D E F (ForgetEnrichment.to (Complex A) P.obj) ≫
      (moduleRestriction A D E F.op).map ((dgModuleExtension A D E F).onClosed.map P.π) at hn
  have hcomp := (moduleQuasiIso A D).comp_mem _ _ P.quasiIso hunit
  rw [hn] at hcomp
  exact (moduleQuasiIso A D).of_postcomp _ _ hg hcomp

lemma dgDerivedExtensionUnit_representable_isIso (hF : HomQuasiIso F) (d : D) :
    IsIso ((dgDerivedExtensionUnit A D E F).app
      ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A d)))) := by
  let M := ForgetEnrichment.of (Complex A) (representable A d)
  let P := moduleCanonicalProjectiveResolution A D M
  have hP := functorExtensionUnit_resolution_quasiIso A D E F
    (representable_homotopicallyProjective A D d)
    (functorExtensionUnit_representable_quasiIso A D E F hF d) P
  have hi := moduleToDerived_inverts A D _ hP
  let := hi
  have h := dgDerivedExtensionUnit_computation A D E F M
  have : IsIso ((dgDerivedExtensionUnit A D E F).app ((moduleToDerived A D).obj M) ≫
      (dgDerivedRestriction A D E F).map
        (dgDerivedExtensionResolutionComputation A D E F P).hom) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right
    ((dgDerivedExtensionUnit A D E F).app ((moduleToDerived A D).obj M))
    ((dgDerivedRestriction A D E F).map
      (dgDerivedExtensionResolutionComputation A D E F P).hom)

end SerrePositivity.DifferentialGraded
end

end FunctorExtensionRepresentableUnit

/-! ## FunctorExtensionUnitAll（旧 SerrePositivity/DifferentialGraded/Derived/FunctorExtensionUnitAll.lean） -/

/-! # Hom準同型に沿う導来単位の全加群上の可逆性

## 概要
Hom準同型に沿う導来単位の全加群上の可逆性。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section FunctorExtensionUnitAll
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance derivedNatTransIsoLocus_stableUnderRetracts
    (G : DerivedModuleCategory A D ⥤ DerivedModuleCategory A D)
    (α : 𝟭 (DerivedModuleCategory A D) ⟶ G) :
    (derivedNatTransIsoLocus A D G α).IsStableUnderRetracts where
  of_retract r hY := by
    exact MorphismProperty.of_retract
      (P := MorphismProperty.isomorphisms (DerivedModuleCategory A D))
      (α.retractArrowApp r) hY

variable (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)
local instance : (dgDerivedRestriction A D E F).CommShift ℤ := dgDerivedRestrictionCommShift A D E F
local instance : (dgDerivedExtension A D E F).CommShift ℤ := dgDerivedExtensionCommShift A D E F
local instance : (dgDerivedRestriction A D E F).IsTriangulated :=
  dgDerivedRestrictionIsTriangulated A D E F
local instance : (dgDerivedExtension A D E F).IsTriangulated :=
  dgDerivedExtensionIsTriangulated A D E F
local instance : (dgDerivedRestriction A D E F).Additive := dgDerivedRestriction_additive A D E F
local instance : (dgDerivedExtension A D E F).Additive := dgDerivedExtension_additive A D E F
local instance : NatTrans.CommShift (dgDerivedExtensionUnit A D E F) ℤ :=
  dgDerivedExtensionUnit_commShift A D E F

lemma dgDerivedRestriction_preservesCoproduct {J : Type u} (G : J → DerivedModuleCategory A E) :
    PreservesColimit (Discrete.functor G) (dgDerivedRestriction A D E F) :=
  derivedAdjunction_rightAdjoint_preservesCoproduct A D E
    (dgDerivedExtension A D E F) (dgDerivedRestriction A D E F)
    (dgDerivedExtensionRestrictionAdjunction A D E F) G
    (fun _ hP => dgDerivedExtension_compact A D E F hP)

instance dgDerivedRestriction_preservesCoproductsOfShape (J : Type u) :
    PreservesColimitsOfShape (Discrete J) (dgDerivedRestriction A D E F) where
  preservesColimit {K} := by
    let := dgDerivedRestriction_preservesCoproduct A D E F (K.obj ∘ Discrete.mk)
    exact preservesColimit_of_iso_diagram _ Discrete.natIsoFunctor.symm

lemma dgDerivedExtensionUnit_isIso_onPerfect (hF : HomQuasiIso F)
    {X : DerivedModuleCategory A D} (hX : modulePerfect A D X) :
    IsIso ((dgDerivedExtensionUnit A D E F).app X) := by
  let P := derivedNatTransIsoLocus A D (dgDerivedExtension A D E F ⋙ dgDerivedRestriction A D E F)
    (dgDerivedExtensionUnit A D E F)
  change P X
  apply ((modulePerfect_le_iff_generators A D P).2 ?_) X hX
  intro d
  exact dgDerivedExtensionUnit_representable_isIso A D E F hF d

/-- Hom準同型性だけで導来単位は全対象で同型。本質的全射性はここでは使わない。 -/
lemma dgDerivedExtensionUnit_isIso_all (hF : HomQuasiIso F) (X : DerivedModuleCategory A D) :
    IsIso ((dgDerivedExtensionUnit A D E F).app X) := by
  let P := derivedNatTransIsoLocus A D (dgDerivedExtension A D E F ⋙ dgDerivedRestriction A D E F)
    (dgDerivedExtensionUnit A D E F)
  change P X
  apply moduleLocalizing_all A D P
  · intro J G hG
    let := (dgDerivedExtensionRestrictionAdjunction A D E F).leftAdjoint_preservesColimits
    exact derivedNatTransIsoLocus_coproduct A D _ (dgDerivedExtensionUnit A D E F) G hG
  · intro Y hY
    exact dgDerivedExtensionUnit_isIso_onPerfect A D E F hF hY

/-- Hom準同型に沿う導来延長は完全忠実。 -/
def dgDerivedExtensionFullyFaithful (hF : HomQuasiIso F) :
    (dgDerivedExtension A D E F).FullyFaithful := by
  letI (X : DerivedModuleCategory A D) :
      IsIso ((dgDerivedExtensionRestrictionAdjunction A D E F).unit.app X) :=
    dgDerivedExtensionUnit_isIso_all A D E F hF X
  letI := NatIso.isIso_of_isIso_app (dgDerivedExtensionRestrictionAdjunction A D E F).unit
  exact (dgDerivedExtensionRestrictionAdjunction A D E F).fullyFaithfulLOfIsIsoUnit

end SerrePositivity.DifferentialGraded
end

end FunctorExtensionUnitAll

/-! ## RestrictionConservative（旧 SerrePositivity/DifferentialGraded/Derived/RestrictionConservative.lean） -/

/-! # 本質的全射なdg関手に沿う導来制限の保守性

## 概要
本質的全射なdg関手に沿う導来制限の保守性。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section RestrictionConservative
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A]

/-- dg Yonedaを主Kへ送り、右加群の主導来圏へ局所化する。 -/
def representableHomotopyToDerived (E : Type w) [DGCategory A E] [Small.{u} E] :
    HomotopyCategory A E ⥤ DerivedModuleCategory A E :=
  (dgYoneda A E).onHomotopy ⋙ moduleHomotopyToDerivedClosed A E

/-- 閉零対象でのYoneda像は実際の代表加群の主導来像。 -/
def representableHomotopyToDerivedComputation (E : Type w) [DGCategory A E] [Small.{u} E]
    (e : ClosedCategory A E) :
    (representableHomotopyToDerived A E).obj ((toHomotopy A E).obj e) ≅
      (moduleToDerived A E).obj
        (ForgetEnrichment.of (Complex A) (representable A (ForgetEnrichment.to (Complex A) e))) :=
  (moduleHomotopyToDerivedClosed A E).mapIso
    (eqToIso (congrArg (fun G => G.obj e) (dgYoneda A E).onHomotopy_fac)) ≪≫
      (moduleToHomotopyDerivedIso A E).app ((dgYoneda A E).onClosed.obj e)

variable (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

lemma dgDerivedExtension_representable_essImage (hF : F.onHomotopy.EssSurj) (e : E) :
    ∃ d : D, Nonempty ((dgDerivedExtension A D E F).obj
      ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A d))) ≅
        (moduleToDerived A E).obj (ForgetEnrichment.of (Complex A) (representable A e))) := by
  let := hF
  let Y := (toHomotopy A E).obj (ForgetEnrichment.of (Complex A) e)
  let X := F.onHomotopy.objPreimage Y
  let d := ForgetEnrichment.to (Complex A) X.as
  let i := F.onHomotopy.objObjPreimageIso Y
  let H := representableHomotopyToDerived A E
  have h₀ := representableHomotopyToDerivedComputation A E (F.onClosed.obj X.as)
  refine ⟨d, ⟨dgDerivedExtensionRepresentableIso A D E F d ≪≫ ?_⟩⟩
  exact h₀.symm ≪≫ H.mapIso i ≪≫
    representableHomotopyToDerivedComputation A E (ForgetEnrichment.of (Complex A) e)

local instance restrictionConservativeCommShift : (dgDerivedRestriction A D E F).CommShift ℤ :=
  dgDerivedRestrictionCommShift A D E F
local instance restrictionConservativeTriangulated :
    (dgDerivedRestriction A D E F).IsTriangulated :=
  dgDerivedRestrictionIsTriangulated A D E F

/-- 主K上の本質的全射性だけから導来制限は零対象を反映する。 -/
lemma dgDerivedRestriction_reflectsZero (hF : F.onHomotopy.EssSurj)
    (X : DerivedModuleCategory A E) (hX : IsZero ((dgDerivedRestriction A D E F).obj X)) :
    IsZero X := by
  apply (moduleRepresentables_detect_zero A E X).mpr
  intro e n
  obtain ⟨d, ⟨ei⟩⟩ := dgDerivedExtension_representable_essImage A D E F hF e
  let R := dgDerivedRestriction A D E F
  have hz : IsZero (R.obj (X⟦n⟧)) :=
    ((shiftFunctor (DerivedModuleCategory A D) n).map_isZero hX).of_iso
      ((R.commShiftIso n).app X)
  let G := (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A d))
  let eh := (Iso.homCongr ei.symm (Iso.refl (X⟦n⟧))).trans
    ((dgDerivedExtensionRestrictionAdjunction A D E F).homEquiv G (X⟦n⟧))
  exact ⟨fun f g => eh.injective (hz.eq_of_tgt (eh f) (eh g))⟩

lemma dgDerivedRestriction_reflectsIso (hF : F.onHomotopy.EssSurj)
    {X Y : DerivedModuleCategory A E} (f : X ⟶ Y)
    [IsIso ((dgDerivedRestriction A D E F).map f)] : IsIso f := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  let T := Triangle.mk f g h
  let R := dgDerivedRestriction A D E F
  have hRT := R.map_distinguished T hT
  have hz : IsZero (R.obj Z) :=
    ((R.mapTriangle.obj T).isZero₃_iff_isIso₁ hRT).2 (by
      change IsIso ((dgDerivedRestriction A D E F).map f)
      infer_instance)
  exact (T.isZero₃_iff_isIso₁ hT).1 (dgDerivedRestriction_reflectsZero A D E F hF Z hz)

lemma dgDerivedRestrictionReflectsIsomorphisms (hF : F.onHomotopy.EssSurj) :
    (dgDerivedRestriction A D E F).ReflectsIsomorphisms where
  reflects f := dgDerivedRestriction_reflectsIso A D E F hF f

end SerrePositivity.DifferentialGraded
end

end RestrictionConservative

/-! ## FunctorDerivedEquivalence（旧 SerrePositivity/DifferentialGraded/Derived/FunctorDerivedEquivalence.lean） -/

/-! # dg準同値に沿う実際の導来延長–制限同値

## 概要
dg準同値に沿う実際の導来延長–制限同値。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section FunctorDerivedEquivalence
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

lemma dgDerivedExtensionCounit_isIso_all (hF : QuasiEquivalence F) (X : DerivedModuleCategory A E) :
    IsIso ((dgDerivedExtensionCounit A D E F).app X) := by
  let adj := dgDerivedExtensionRestrictionAdjunction A D E F
  let R := dgDerivedRestriction A D E F
  have hu : IsIso (adj.unit.app (R.obj X)) := dgDerivedExtensionUnit_isIso_all A D E F hF.1 _
  let := hu
  have he : R.map (adj.counit.app X) = inv (adj.unit.app (R.obj X)) := by
    apply (cancel_epi (adj.unit.app (R.obj X))).1
    rw [adj.right_triangle_components, IsIso.hom_inv_id]
    rfl
  have hm : IsIso (R.map (adj.counit.app X)) := by rw [he]; infer_instance
  let := hm
  exact dgDerivedRestriction_reflectsIso A D E F hF.2 (adj.counit.app X)

/-- 各Homの準同型と主Kの本質的全射性から、全右加群の主導来圏の同値を構成する。 -/
def dgFunctorDerivedEquivalence (hF : QuasiEquivalence F) :
    DerivedModuleCategory A D ≌ DerivedModuleCategory A E := by
  letI (X : DerivedModuleCategory A D) :
      IsIso ((dgDerivedExtensionRestrictionAdjunction A D E F).unit.app X) :=
    dgDerivedExtensionUnit_isIso_all A D E F hF.1 X
  letI (Y : DerivedModuleCategory A E) :
      IsIso ((dgDerivedExtensionRestrictionAdjunction A D E F).counit.app Y) :=
    dgDerivedExtensionCounit_isIso_all A D E F hF Y
  exact (dgDerivedExtensionRestrictionAdjunction A D E F).toEquivalence

lemma dgFunctorDerivedEquivalence_functor (hF : QuasiEquivalence F) :
    (dgFunctorDerivedEquivalence A D E F hF).functor = dgDerivedExtension A D E F := rfl

lemma dgFunctorDerivedEquivalence_inverse (hF : QuasiEquivalence F) :
    (dgFunctorDerivedEquivalence A D E F hF).inverse = dgDerivedRestriction A D E F := rfl

lemma dgFunctorDerivedEquivalence_unit (hF : QuasiEquivalence F) :
    (dgFunctorDerivedEquivalence A D E F hF).unitIso.hom = dgDerivedExtensionUnit A D E F := rfl

lemma dgFunctorDerivedEquivalence_counit (hF : QuasiEquivalence F) :
    (dgFunctorDerivedEquivalence A D E F hF).counitIso.hom = dgDerivedExtensionCounit A D E F := rfl

end SerrePositivity.DifferentialGraded
end

end FunctorDerivedEquivalence

/-! ## FunctorExtensionKFlatUnit（旧 SerrePositivity/DifferentialGraded/Derived/FunctorExtensionKFlatUnit.lean） -/

/-! # 相対K-flat右加群上の延長単位と準同値に沿う制限の準同型反映

## 概要
相対K-flat右加群上の延長単位と準同値に沿う制限の準同型反映。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section FunctorExtensionKFlatUnit
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- graph延長は右相対K-flat加群間の準同型を保つ。 -/
lemma dgModuleExtension_relativeKFlat_quasiIso {M N : ModuleCategory A D}
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M))
    (hN : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) N))
    (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    moduleQuasiIso A E ((dgModuleExtension A D E F).onClosed.map f) := by
  intro e
  rw [dgModuleExtension_map_eval]
  exact BalancedTensor.rightTensor_relativeKFlat_quasiIso A D
    ((functorGraph A D E F).leftAt e) hM hN f hf

/-- Hom準同型に沿う単位は標準の射影解像度上で準同型。 -/
lemma functorExtensionUnit_canonical_quasiIso (hF : HomQuasiIso F) (M : ModuleCategory A D) :
    moduleQuasiIso A D (functorExtensionUnit A D E F
      (ForgetEnrichment.to (Complex A) (moduleCanonicalProjectiveResolution A D M).obj)) := by
  let P := moduleCanonicalProjectiveResolution A D M
  let i := moduleDerivedIso A D P.π P.quasiIso
  let c := dgDerivedRestrictionComputation A D E F
    ((dgModuleExtension A D E F).onClosed.obj P.obj)
  let η := functorExtensionUnit A D E F (ForgetEnrichment.to (Complex A) P.obj)
  have hu := dgDerivedExtensionUnit_isIso_all A D E F hF ((moduleToDerived A D).obj M)
  let := hu
  have h := dgDerivedExtensionUnit_computation A D E F M
  have hc : IsIso (i.inv ≫ (moduleToDerived A D).map η ≫ c.inv) := by
    rw [← h]
    infer_instance
  let := hc
  have ht : IsIso ((moduleToDerived A D).map η ≫ c.inv) :=
    IsIso.of_isIso_comp_left i.inv _
  let := ht
  exact (moduleToDerived_map_isIso_iff A D η).mp
    (IsIso.of_isIso_comp_right ((moduleToDerived A D).map η) c.inv)

/-- Hom準同型に沿う実際の単位は任意の右相対K-flat加群上で準同型。 -/
lemma functorExtensionUnit_relativeKFlat_quasiIso (hF : HomQuasiIso F)
    (M : ModuleCategory A D)
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M)) :
    moduleQuasiIso A D (functorExtensionUnit A D E F
      (ForgetEnrichment.to (Complex A) M)) := by
  let P := moduleCanonicalProjectiveResolution A D M
  have hP := moduleHomotopicallyProjective_relativeKFlat A D P.projective
  have he := dgModuleExtension_relativeKFlat_quasiIso A D E F hP hM P.π P.quasiIso
  have hr := moduleRestriction_quasiIso A D E F.op _ he
  have hu := functorExtensionUnit_canonical_quasiIso A D E F hF M
  have hn := (dgModuleUnit A D E F).naturality P.π
  change P.π ≫ functorExtensionUnit A D E F (ForgetEnrichment.to (Complex A) M) =
    functorExtensionUnit A D E F (ForgetEnrichment.to (Complex A) P.obj) ≫
      (moduleRestriction A D E F.op).map ((dgModuleExtension A D E F).onClosed.map P.π) at hn
  have hc := (moduleQuasiIso A D).comp_mem _ _ hu hr
  rw [← hn] at hc
  exact (moduleQuasiIso A D).of_precomp _ _ P.quasiIso hc

/-- 本質的全射なdg関手の制限は、全右加群射の準同型性を反映する。 -/
lemma moduleRestriction_reflects_quasiIso (hF : F.onHomotopy.EssSurj)
    {M N : ModuleCategory A E} (f : M ⟶ N)
    (hf : moduleQuasiIso A D ((moduleRestriction A D E F.op).map f)) :
    moduleQuasiIso A E f := by
  have hi := moduleToDerived_inverts A D _ hf
  have hi' : IsIso ((moduleToDerived A E ⋙ dgDerivedRestriction A D E F).map f) := by
    rw [dgDerivedRestriction_fac]
    exact hi
  have : IsIso ((dgDerivedRestriction A D E F).map ((moduleToDerived A E).map f)) := hi'
  exact (moduleToDerived_map_isIso_iff A E f).mp
    (dgDerivedRestriction_reflectsIso A D E F hF ((moduleToDerived A E).map f))

/-- 制限への指定射を閉零の延長–制限随伴で転置した実際の加群射。 -/
def functorExtensionTranspose {R : ModuleCategory A D} {M : ModuleCategory A E}
    (q : R ⟶ (moduleRestriction A D E F.op).obj M) :
    (dgModuleExtension A D E F).onClosed.obj R ⟶ M :=
  ((dgModuleExtensionRestrictionAdjunction A D E F).homEquiv R M).symm q

lemma functorExtensionTranspose_eq {R : ModuleCategory A D} {M : ModuleCategory A E}
    (q : R ⟶ (moduleRestriction A D E F.op).obj M) :
    functorExtensionTranspose A D E F q =
      (dgModuleExtension A D E F).onClosed.map q ≫
        functorExtensionCounit A D E F (ForgetEnrichment.to (Complex A) M) :=
  (dgModuleExtensionRestrictionAdjunction A D E F).homEquiv_counit _ _ q

lemma functorExtensionTranspose_unit_fac {R : ModuleCategory A D} {M : ModuleCategory A E}
    (q : R ⟶ (moduleRestriction A D E F.op).obj M) :
    functorExtensionUnit A D E F (ForgetEnrichment.to (Complex A) R) ≫
        (moduleRestriction A D E F.op).map (functorExtensionTranspose A D E F q) = q :=
  ((dgModuleExtensionRestrictionAdjunction A D E F).homEquiv_unit _ _
    (functorExtensionTranspose A D E F q)).symm.trans
      (Equiv.apply_symm_apply _ q)

/-- 準同値に沿い、制限への右K-flat準同型を転置すると再び準同型になる。 -/
lemma functorExtensionTranspose_quasiIso (hF : QuasiEquivalence F)
    {R : ModuleCategory A D} {M : ModuleCategory A E}
    (hR : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) R))
    (q : R ⟶ (moduleRestriction A D E F.op).obj M) (hq : moduleQuasiIso A D q) :
    moduleQuasiIso A E (functorExtensionTranspose A D E F q) := by
  apply moduleRestriction_reflects_quasiIso A D E F hF.2
  have hu := functorExtensionUnit_relativeKFlat_quasiIso A D E F hF.1 R hR
  have hc : moduleQuasiIso A D
      (functorExtensionUnit A D E F (ForgetEnrichment.to (Complex A) R) ≫
        (moduleRestriction A D E F.op).map (functorExtensionTranspose A D E F q)) := by
    rw [functorExtensionTranspose_unit_fac]
    exact hq
  exact (moduleQuasiIso A D).of_precomp _ _ hu hc

end SerrePositivity.DifferentialGraded
end

end FunctorExtensionKFlatUnit

/-! ## BimoduleRestrictionEquivalence（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleRestrictionEquivalence.lean） -/

/-! # 明示した局所K-flat性の下での導来bimodule制限の同値性

## 概要
明示した局所K-flat性の下での導来bimodule制限の同値性。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleRestrictionEquivalence
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (F : DGFunctor A B D) (G : DGFunctor A C E)

def bimoduleRestrictionModuleDerived :
    DerivedModuleCategory A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ ⥤
      DerivedModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ :=
  moduleDerivedRestriction A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ (DGTensorCategory A Dᵒᵖ E)ᵒᵖ
    (bimoduleRestrictionIndex A B C D E F G)

lemma bimoduleRestrictionModuleDerived_fac :
    moduleToDerived A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ ⋙
        bimoduleRestrictionModuleDerived A B C D E F G =
      moduleRestriction A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ (DGTensorCategory A Dᵒᵖ E)ᵒᵖ
        (bimoduleRestrictionIndex A B C D E F G) ⋙
          moduleToDerived A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ :=
  moduleDerivedRestriction_fac _ _ _ _

/-- 制限の積dg圏表示は、閉零の右加群–bimodule比較と自然に可換。 -/
def bimoduleRestrictionModuleIso :
    bimoduleRestriction A B C D E F G ⋙ (rightModuleBimoduleEquivalence A B C).inverse ≅
      (rightModuleBimoduleEquivalence A D E).inverse ⋙
        moduleRestriction A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ (DGTensorCategory A Dᵒᵖ E)ᵒᵖ
          (bimoduleRestrictionIndex A B C D E F G) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (rightModuleBimoduleEquivalence A D E).inverse
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (rightModuleBimoduleEquivalence A B C).unitIso.symm ≪≫
          Functor.rightUnitor _)

/-- 既存の実際の導来bimodule制限を右加群の導来制限と比較する全射自然な正方形。 -/
def derivedBimoduleRestrictionModuleIso :
    derivedBimoduleRestriction A B C D E F G ⋙
        (rightModuleBimoduleDerivedEquivalence A B C).inverse ≅
      (rightModuleBimoduleDerivedEquivalence A D E).inverse ⋙
        bimoduleRestrictionModuleDerived A B C D E F G := by
  let Q₁ := bimoduleToDerived A D E
  let W₁ := BimoduleCategory.quasiIso A D E
  let M₁ := moduleToDerived A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ
  let M₂ := moduleToDerived A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
  let E₁ := rightModuleBimoduleDerivedEquivalence A D E
  let E₂ := rightModuleBimoduleDerivedEquivalence A B C
  let R₀ := bimoduleRestriction A B C D E F G
  let R := bimoduleRestrictionModuleDerived A B C D E F G
  let S := derivedBimoduleRestriction A B C D E F G
  let U := (R₀ ⋙ bimoduleToDerived A B C) ⋙ E₂.inverse
  let V := bimoduleToModuleDerived A D E ⋙ R
  letI : Localization.Lifting Q₁ W₁ U (S ⋙ E₂.inverse) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (eqToIso (derivedBimoduleRestriction_fac A B C D E F G)) E₂.inverse⟩
  letI : Localization.Lifting Q₁ W₁ V (E₁.inverse ⋙ R) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (rightModuleBimoduleDerived_inverse_fac A D E) R⟩
  apply Localization.liftNatIso Q₁ W₁ U V (S ⋙ E₂.inverse) (E₁.inverse ⋙ R)
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft R₀ (rightModuleBimoduleDerived_inverse_fac A B C) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (bimoduleRestrictionModuleIso A B C D E F G) M₂ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (rightModuleBimoduleEquivalence A D E).inverse
      (eqToIso (bimoduleRestrictionModuleDerived_fac A B C D E F G)).symm ≪≫
    (Functor.associator _ M₁ R).symm

omit [Small.{u} B] [Small.{u} C] [Small.{u} D] [Small.{u} E] in
lemma bimoduleRestrictionDG_quasiEquivalence (hF : QuasiEquivalence F) (hG : QuasiEquivalence G)
    (hC : localHomKFlat A C) (hD : localHomKFlat A D) :
    QuasiEquivalence (F.op.tensor G).op :=
  quasiEquivalence_op _ (quasiEquivalence_tensor F.op G (quasiEquivalence_op F hF) hG hC
    (fun x y => hD y.unop x.unop))

lemma derivedBimoduleRestriction_isEquivalence (hF : QuasiEquivalence F) (hG : QuasiEquivalence G)
    (hC : localHomKFlat A C) (hD : localHomKFlat A D) :
    (derivedBimoduleRestriction A B C D E F G).IsEquivalence := by
  let R := bimoduleRestrictionModuleDerived A B C D E F G
  have : R.IsEquivalence :=
    (dgFunctorDerivedEquivalence A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
      (DGTensorCategory A Dᵒᵖ E)ᵒᵖ (F.op.tensor G).op
      (bimoduleRestrictionDG_quasiEquivalence A B C D E F G hF hG hC hD)).isEquivalence_inverse
  have : ((rightModuleBimoduleDerivedEquivalence A D E).inverse ⋙ R).IsEquivalence := inferInstance
  have : (derivedBimoduleRestriction A B C D E F G ⋙
      (rightModuleBimoduleDerivedEquivalence A B C).inverse).IsEquivalence :=
    Functor.isEquivalence_of_iso (derivedBimoduleRestrictionModuleIso A B C D E F G).symm
  exact Functor.isEquivalence_of_comp_right _ (rightModuleBimoduleDerivedEquivalence A B C).inverse

/-- 指定された実際の導来制限を順方向とする同値。 -/
def derivedBimoduleRestrictionEquivalence (hF : QuasiEquivalence F) (hG : QuasiEquivalence G)
    (hC : localHomKFlat A C) (hD : localHomKFlat A D) :
    DerivedBimoduleCategory A D E ≌ DerivedBimoduleCategory A B C := by
  letI := derivedBimoduleRestriction_isEquivalence A B C D E F G hF hG hC hD
  exact (derivedBimoduleRestriction A B C D E F G).asEquivalence

end SerrePositivity.DifferentialGraded
end

end BimoduleRestrictionEquivalence

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "4.6.2.17" (partial := special) "仮定：通常の可換環の準同型、または小さい dg 圏の dg 関手（Lean が強い：通常圏と通常の導来圏に限る）。結論：加群の制限に対してテンソルによる拡大が左随伴となり、dg では導来拡大・制限にも随伴を構成する（この仮定での HA の結論の一部に一致）。一般の左テンソル ∞ 圏は含まれない。"] _root_.SerrePositivity.DifferentialGraded.dgDerivedExtensionRestrictionAdjunction
