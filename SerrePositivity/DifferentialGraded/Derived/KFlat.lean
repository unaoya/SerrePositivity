module

public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensor
public import SerrePositivity.DifferentialGraded.Tensor.Associator.Pentagon
public import SerrePositivity.DifferentialGraded.Bimodule.Right
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.KFlatness
public import SerrePositivity.DifferentialGraded.Derived.Projective
public import SerrePositivity.DifferentialGraded.Bimodule.Value

/-!
# Derived.KFlat

## 概要
10 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## RightKFlatComposition（旧 SerrePositivity/DifferentialGraded/Derived/RightKFlatComposition.lean） -/

/-! # 右相対K-flatな対象の充満部分圏での合成と導来比較

## 概要
右相対K-flatな対象の充満部分圏での合成と導来比較。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionPairResolution.lean、
Derived/BimoduleTensorPentagon.lean。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section RightKFlatComposition
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

/-- 既存の合成対象とK-flat合成閉性の証拠を、同じ充満部分圏に束ねる。 -/
def rightKFlatCompose (Q : RightKFlatBimoduleCategory A C E)
    (R : RightKFlatBimoduleCategory A E F) : RightKFlatBimoduleCategory A C F :=
  ⟨BimoduleCategory.of A C F (compose A C E F (BimoduleCategory.underlying A C E Q.obj)
      (BimoduleCategory.underlying A E F R.obj)),
    Bimodule.rightRelativeKFlat_compose A C E F (BimoduleCategory.underlying A C E Q.obj)
      (BimoduleCategory.underlying A E F R.obj) Q.property R.property⟩

/-- 右K-flat対象の型付き表示に対する既存の導来合成関手。 -/
abbrev rightKFlatDerivedCompose (Q : RightKFlatBimoduleCategory A C E) :=
  derivedComposeWith A B C E Q.obj Q.property

def rightKFlatDerivedMap {Q Q' : RightKFlatBimoduleCategory A C E} (g : Q.obj ⟶ Q'.obj) :
    rightKFlatDerivedCompose A B C E Q ⟶ rightKFlatDerivedCompose A B C E Q' :=
  derivedComposeWithMap A B C E Q.property Q'.property g

def rightKFlatDerivedAssociator (Q : RightKFlatBimoduleCategory A C E)
    (R : RightKFlatBimoduleCategory A E F) :
    rightKFlatDerivedCompose A B C E Q ⋙ rightKFlatDerivedCompose A B E F R ≅
      rightKFlatDerivedCompose A B C F (rightKFlatCompose A C E F Q R) :=
  derivedAssociatorIso A B C E F Q.obj R.obj Q.property R.property

omit [Small.{u} E] in
lemma rightKFlatDerivedCompose_map_base (Q : RightKFlatBimoduleCategory A C E)
    {P P' : BimoduleCategory A B C} (f : P ⟶ P') :
    (rightKFlatDerivedCompose A B C E Q).map ((bimoduleToDerived A B C).map f) =
      (bimoduleToDerived A B E).map (composeMap A B C E f (𝟙 Q.obj)) :=
  derivedComposeWith_map_base A B C E Q.obj Q.property f

omit [Small.{u} E] in
lemma rightKFlatDerivedMap_base_app {Q Q' : RightKFlatBimoduleCategory A C E}
    (g : Q.obj ⟶ Q'.obj) (P : BimoduleCategory A B C) :
    (rightKFlatDerivedMap A B C E g).app ((bimoduleToDerived A B C).obj P) =
      (bimoduleToDerived A B E).map (composeMap A B C E (𝟙 P) g) :=
  derivedComposeWithMap_base_app A B C E Q.property Q'.property g P

lemma rightKFlatDerivedAssociator_base_app (Q : RightKFlatBimoduleCategory A C E)
    (R : RightKFlatBimoduleCategory A E F) (P : BimoduleCategory A B C) :
    (rightKFlatDerivedAssociator A B C E F Q R).hom.app ((bimoduleToDerived A B C).obj P) =
      (bimoduleToDerived A B F).map
        (associatorIso A B C E F (BimoduleCategory.underlying A B C P)
          (BimoduleCategory.underlying A C E Q.obj) (BimoduleCategory.underlying A E F R.obj)).hom
      :=
  derivedAssociatorIso_base_app A B C E F Q.obj R.obj Q.property R.property P

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end RightKFlatComposition

/-! ## BimoduleTensorPentagon（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleTensorPentagon.lean） -/

/-! # 三つの固定右K-flat因子に関する導来合成の五角coherence

## 概要
三つの固定右K-flat因子に関する導来合成の五角coherence。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionPentagonInner.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleTensorPentagon
universe u v w z t x

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  (F : Type t) (G : Type x)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F] [DGCategory A G]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]

lemma derivedPentagon (Q : RightKFlatBimoduleCategory A C E)
    (R : RightKFlatBimoduleCategory A E F) (S : RightKFlatBimoduleCategory A F G) :
    whiskerLeft (rightKFlatDerivedCompose A B C E Q)
        (rightKFlatDerivedAssociator A B E F G R S).hom ≫
      (rightKFlatDerivedAssociator A B C E G Q (rightKFlatCompose A E F G R S)).hom =
    whiskerRight (rightKFlatDerivedAssociator A B C E F Q R).hom
        (rightKFlatDerivedCompose A B F G S) ≫
      (rightKFlatDerivedAssociator A B C F G (rightKFlatCompose A C E F Q R) S).hom ≫
      rightKFlatDerivedMap A B C G
        (Q := rightKFlatCompose A C F G (rightKFlatCompose A C E F Q R) S)
        (Q' := rightKFlatCompose A C E G Q (rightKFlatCompose A E F G R S))
        (associatorIso A C E F G (BimoduleCategory.underlying A C E Q.obj)
          (BimoduleCategory.underlying A E F R.obj) (BimoduleCategory.underlying A F G S.obj)).hom
      := by
  apply bimoduleDerivedNatTrans_ext A B C
  intro P
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    rightKFlatDerivedAssociator_base_app]
  have hm : (rightKFlatDerivedAssociator A B E F G R S).hom.app
      ((rightKFlatDerivedCompose A B C E Q).obj ((bimoduleToDerived A B C).obj P)) =
      (bimoduleToDerived A B G).map
        (associatorIso A B E F G
          (compose A B C E (BimoduleCategory.underlying A B C P)
            (BimoduleCategory.underlying A C E Q.obj))
          (BimoduleCategory.underlying A E F R.obj) (BimoduleCategory.underlying A F G S.obj)).hom
      :=
    rightKFlatDerivedAssociator_base_app A B E F G R S
      (BimoduleCategory.of A B E (compose A B C E
        (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q.obj)))
  rw [hm]
  simp only [rightKFlatDerivedCompose, rightKFlatDerivedMap,
    derivedComposeWith_map_base, derivedComposeWithMap_base_app,
    ← CategoryTheory.Functor.map_comp]
  exact congrArg (fun f => (bimoduleToDerived A B G).map f)
    (pentagon A B C E F G (BimoduleCategory.underlying A B C P)
      (BimoduleCategory.underlying A C E Q.obj) (BimoduleCategory.underlying A E F R.obj)
      (BimoduleCategory.underlying A F G S.obj))

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleTensorPentagon

/-! ## KFlatBimoduleLocalization（旧 SerrePositivity/DifferentialGraded/Derived/KFlatBimoduleLocalization.lean） -/

/-! # 右相対K-flat因子の準同型局所化上の導来合成関手

## 概要
右相対K-flat因子の準同型局所化上の導来合成関手。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/KFlatBimoduleHomotopy.lean、Derived/
KFlatBimoduleResolution.lean。固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section KFlatBimoduleLocalization
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

omit [DGCategory A B] [Small.{u} B] in
def rightKFlatInclusion : RightKFlatBimoduleCategory A C E ⥤ BimoduleCategory A C E :=
  ObjectProperty.ι _

omit [DGCategory A B] [Small.{u} B] in
def rightKFlatQuasiIso : MorphismProperty (RightKFlatBimoduleCategory A C E) :=
  (BimoduleCategory.quasiIso A C E).inverseImage (rightKFlatInclusion A C E)

omit [DGCategory A B] [Small.{u} B] in
abbrev DerivedRightKFlatBimoduleCategory := (rightKFlatQuasiIso A C E).Localization

omit [DGCategory A B] [Small.{u} B] in
abbrev rightKFlatToDerived : RightKFlatBimoduleCategory A C E ⥤
    DerivedRightKFlatBimoduleCategory A C E := (rightKFlatQuasiIso A C E).Q

omit [DGCategory A B] [Small.{u} B] in
def rightKFlatDerivedInclusion : DerivedRightKFlatBimoduleCategory A C E ⥤
    DerivedBimoduleCategory A C E :=
  Localization.Construction.lift (rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E)
    (fun _ _ f hf => bimoduleToDerived_inverts A C E f.hom hf)

omit [DGCategory A B] [Small.{u} B] in
lemma rightKFlatDerivedInclusion_fac :
    rightKFlatToDerived A C E ⋙ rightKFlatDerivedInclusion A C E =
      rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E :=
  Localization.Construction.fac _ _

lemma derivedComposeWithFunctor_inverts :
    (rightKFlatQuasiIso A C E).IsInvertedBy (derivedComposeWithFunctor A B C E) := by
  intro Q Q' g hg
  change IsIso (derivedComposeWithMap A B C E Q.property Q'.property g.hom)
  change IsIso (derivedComposeWithKFlatIso A B C E Q.property Q'.property g.hom hg).hom
  infer_instance

/-- 前の変数の導来圏に値を持つ関手族を、後のK-flat因子の局所化へ降下させる。 -/
def rightFactorLocalizedComposeFunctor : DerivedRightKFlatBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E) :=
  Localization.Construction.lift (derivedComposeWithFunctor A B C E)
    (derivedComposeWithFunctor_inverts A B C E)

lemma rightFactorLocalizedComposeFunctor_fac :
    rightKFlatToDerived A C E ⋙ rightFactorLocalizedComposeFunctor A B C E =
      derivedComposeWithFunctor A B C E := Localization.Construction.fac _ _

lemma rightFactorLocalizedComposeFunctor_map_base {Q Q' : RightKFlatBimoduleCategory A C E}
    (g : Q ⟶ Q') :
    (rightFactorLocalizedComposeFunctor A B C E).map ((rightKFlatToDerived A C E).map g) =
      (derivedComposeWithFunctor A B C E).map g :=
  eq_of_heq (Functor.hcongr_hom (rightFactorLocalizedComposeFunctor_fac A B C E) g)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end KFlatBimoduleLocalization

/-! ## KFlatBimoduleHomotopy（旧 SerrePositivity/DifferentialGraded/Derived/KFlatBimoduleHomotopy.lean） -/

/-! # K-flat部分圏の局所化で全dg自然な加群ホモトピーを同一視する

## 概要
K-flat部分圏の局所化で全dg自然な加群ホモトピーを同一視する。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/KFlatBimoduleReplacement.lean。固定dg圏上の導来tensor・
Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section KFlatBimoduleHomotopy
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

def rightKFlatOfModule (M : ModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ)
    (hM : Bimodule.rightRelativeKFlat A B C (BimoduleCategory.underlying A B C
      ((rightModuleBimoduleEquivalence A B C).functor.obj M))) : RightKFlatBimoduleCategory A B C :=
  ⟨(rightModuleBimoduleEquivalence A B C).functor.obj M, hM⟩

def rightKFlatOfModuleMap {M N : ModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ}
    (hM) (hN) (f : M ⟶ N) : rightKFlatOfModule A B C M hM ⟶ rightKFlatOfModule A B C N hN :=
  ObjectProperty.homMk ((rightModuleBimoduleEquivalence A B C).functor.map f)

lemma rightKFlatOfModuleMap_id (M : ModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ) (hM) :
    rightKFlatOfModuleMap A B C hM hM (𝟙 M) = 𝟙 (rightKFlatOfModule A B C M hM) := by
  apply ObjectProperty.hom_ext
  exact (rightModuleBimoduleEquivalence A B C).functor.map_id M

lemma rightKFlatOfModuleMap_comp {M N P : ModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ}
    (hM) (hN) (hP) (f : M ⟶ N) (g : N ⟶ P) :
    rightKFlatOfModuleMap A B C hM hP (f ≫ g) =
      rightKFlatOfModuleMap A B C hM hN f ≫ rightKFlatOfModuleMap A B C hN hP g := by
  apply ObjectProperty.hom_ext
  exact (rightModuleBimoduleEquivalence A B C).functor.map_comp f g

lemma rightKFlat_equalizes_source_boundary
    {M N : ModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ}
    (hM : Bimodule.rightRelativeKFlat A B C (BimoduleCategory.underlying A B C
      ((rightModuleBimoduleEquivalence A B C).functor.obj M)))
    (hN : Bimodule.rightRelativeKFlat A B C (BimoduleCategory.underlying A B C
      ((rightModuleBimoduleEquivalence A B C).functor.obj N)))
    (f g : M ⟶ N) (h : boundaryRelation A (RightModule A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ) f g) :
    (rightKFlatToDerived A B C).map (rightKFlatOfModuleMap A B C hM hN f) =
      (rightKFlatToDerived A B C).map (rightKFlatOfModuleMap A B C hM hN g) := by
  let P := modulePrecylinder A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ M
  let hI := rightModuleBimodule_cylinder_rightRelativeKFlat A B C M hM
  let i₀ := rightKFlatOfModuleMap A B C hM hI P.i₀
  let i₁ := rightKFlatOfModuleMap A B C hM hI P.i₁
  let π := rightKFlatOfModuleMap A B C hI hM P.π
  let d := rightKFlatOfModuleMap A B C hI hN (moduleCylinderDesc A _ f g h)
  have h₀π : i₀ ≫ π = 𝟙 (rightKFlatOfModule A B C M hM) := by
    rw [← rightKFlatOfModuleMap_comp, P.i₀_π, rightKFlatOfModuleMap_id]
  have h₁π : i₁ ≫ π = 𝟙 (rightKFlatOfModule A B C M hM) := by
    rw [← rightKFlatOfModuleMap_comp, P.i₁_π, rightKFlatOfModuleMap_id]
  have h₀d : i₀ ≫ d = rightKFlatOfModuleMap A B C hM hN f := by
    rw [← rightKFlatOfModuleMap_comp, moduleCylinderDesc_i₀]
  have h₁d : i₁ ≫ d = rightKFlatOfModuleMap A B C hM hN g := by
    rw [← rightKFlatOfModuleMap_comp, moduleCylinderDesc_i₁]
  have hπ : rightKFlatQuasiIso A B C π :=
    (rightModuleBimoduleEquivalence_quasiIso_iff A B C P.π).2
      (modulePrecylinder_π_quasiIso A _ M)
  let e := Localization.Construction.wIso (W := rightKFlatQuasiIso A B C) π hπ
  have hi : (rightKFlatToDerived A B C).map i₀ = (rightKFlatToDerived A B C).map i₁ := by
    apply (Iso.cancel_iso_hom_right _ _ e).1
    exact ((rightKFlatToDerived A B C).map_comp i₀ π).symm.trans
      ((congrArg (rightKFlatToDerived A B C).map h₀π).trans
        ((congrArg (rightKFlatToDerived A B C).map h₁π.symm).trans
          ((rightKFlatToDerived A B C).map_comp i₁ π)))
  calc
    _ = (rightKFlatToDerived A B C).map (i₀ ≫ d) := congrArg _ h₀d.symm
    _ = (rightKFlatToDerived A B C).map i₀ ≫ (rightKFlatToDerived A B C).map d :=
      (rightKFlatToDerived A B C).map_comp _ _
    _ = (rightKFlatToDerived A B C).map i₁ ≫ (rightKFlatToDerived A B C).map d :=
      congrArg (fun k => k ≫ (rightKFlatToDerived A B C).map d) hi
    _ = _ := ((rightKFlatToDerived A B C).map_comp i₁ d).symm.trans (congrArg _ h₁d)

lemma rightKFlat_map_eq_of_source_homotopy
    {M N : ModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ}
    (hM : Bimodule.rightRelativeKFlat A B C (BimoduleCategory.underlying A B C
      ((rightModuleBimoduleEquivalence A B C).functor.obj M)))
    (hN : Bimodule.rightRelativeKFlat A B C (BimoduleCategory.underlying A B C
      ((rightModuleBimoduleEquivalence A B C).functor.obj N)))
    (f g : M ⟶ N)
    (h : (moduleToHomotopy A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ).map f =
      (moduleToHomotopy A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ).map g) :
    (rightKFlatToDerived A B C).map (rightKFlatOfModuleMap A B C hM hN f) =
      (rightKFlatToDerived A B C).map (rightKFlatOfModuleMap A B C hM hN g) :=
  rightKFlat_equalizes_source_boundary A B C hM hN f g
    ((moduleHomotopy_nonempty_iff A _ f g).1 ((moduleToHomotopy_map_eq_iff A _ f g).1 h))

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end KFlatBimoduleHomotopy

/-! ## KFlatBimoduleResolution（旧 SerrePositivity/DifferentialGraded/Derived/KFlatBimoduleResolution.lean） -/

/-! # 右相対K-flat部分圏の局所化から導来bimodule圏への対象の到達性

## 概要
右相対K-flat部分圏の局所化から導来bimodule圏への対象の到達性。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/KFlatBimoduleReplacement.lean。固定dg圏上の導来tensor・
Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section KFlatBimoduleResolution
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (C : Type v) (E : Type w)
  [DGCategory A C] [DGCategory A E] [Small.{u} C] [Small.{u} E]

def rightKFlatResolutionObj (hE : localHomKFlat A E) (M : BimoduleCategory A C E) :
    RightKFlatBimoduleCategory A C E :=
  ⟨(bimoduleCanonicalSemifreeResolution A C E M).obj,
    (bimoduleCanonicalSemifreeResolution A C E M).rightRelativeKFlat A C E hE⟩

def rightKFlatResolutionDerivedIso (hE : localHomKFlat A E) (M : BimoduleCategory A C E) :
    (rightKFlatDerivedInclusion A C E).obj
        ((rightKFlatToDerived A C E).obj (rightKFlatResolutionObj A C E hE M)) ≅
      (bimoduleToDerived A C E).obj M :=
  bimoduleDerivedIso A C E (bimoduleCanonicalSemifreeResolution A C E M).π
    (bimoduleCanonicalSemifreeResolution A C E M).quasiIso

/-- 本質的全射性のみ。充満忠実性をこの段階では仮定しない。 -/
lemma rightKFlatDerivedInclusion_essSurj (hE : localHomKFlat A E) :
    (rightKFlatDerivedInclusion A C E).EssSurj where
  mem_essImage X := by
    obtain ⟨M, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (bimoduleToDerived A C E) X
    exact ⟨(rightKFlatToDerived A C E).obj (rightKFlatResolutionObj A C E hE M),
      ⟨rightKFlatResolutionDerivedIso A C E hE M ≪≫ e⟩⟩

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end KFlatBimoduleResolution

/-! ## KFlatBimoduleReplacement（旧 SerrePositivity/DifferentialGraded/Derived/KFlatBimoduleReplacement.lean） -/

/-! # 導来bimodule圏からK-flat部分圏の局所化への置換関手

## 概要
導来bimodule圏からK-flat部分圏の局所化への置換関手。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/KFlatBimoduleAugmentation.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section KFlatBimoduleReplacement
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

lemma rightModuleBimodule_inverse_quasiIso_iff {M N : BimoduleCategory A B C} (f : M ⟶ N) :
    moduleQuasiIso A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
        ((rightModuleBimoduleEquivalence A B C).inverse.map f) ↔
      BimoduleCategory.quasiIso A B C f := by
  rw [← rightModuleBimoduleEquivalence_quasiIso_iff]
  let E := rightModuleBimoduleEquivalence A B C
  let W := BimoduleCategory.quasiIso A B C
  change W (E.functor.map (E.inverse.map f)) ↔ W f
  calc
    W (E.functor.map (E.inverse.map f)) ↔
        W (E.functor.map (E.inverse.map f) ≫ (E.counitIso.app N).hom) :=
      (W.cancel_right_of_respectsIso _ _).symm
    _ ↔ W ((E.counitIso.app M).hom ≫ f) :=
      Iff.of_eq (congrArg (fun k => W k) (E.counitIso.hom.naturality f))
    _ ↔ W f := W.cancel_left_of_respectsIso _ _

def bimoduleSourceProjectiveResolution (M : BimoduleCategory A B C) :
    ModuleProjectiveResolution A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
      ((rightModuleBimoduleEquivalence A B C).inverse.obj M) :=
  moduleCanonicalProjectiveResolution A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
    ((rightModuleBimoduleEquivalence A B C).inverse.obj M)

def rightKFlatReplacementMap (hC : localHomKFlat A C) {M N : BimoduleCategory A B C} (f : M ⟶ N) :
    rightKFlatResolutionObj A B C hC M ⟶ rightKFlatResolutionObj A B C hC N :=
  rightKFlatOfModuleMap A B C
    (rightKFlatResolutionObj A B C hC M).property (rightKFlatResolutionObj A B C hC N).property
    ((bimoduleSourceProjectiveResolution A B C M).lift
      (bimoduleSourceProjectiveResolution A B C N)
      ((rightModuleBimoduleEquivalence A B C).inverse.map f))

lemma rightKFlatReplacementMap_id (hC : localHomKFlat A C) (M : BimoduleCategory A B C) :
    (rightKFlatToDerived A B C).map (rightKFlatReplacementMap A B C hC (𝟙 M)) =
      𝟙 ((rightKFlatToDerived A B C).obj (rightKFlatResolutionObj A B C hC M)) := by
  have h := (bimoduleSourceProjectiveResolution A B C M).lift_id
  rw [← (rightModuleBimoduleEquivalence A B C).inverse.map_id M] at h
  have he := rightKFlat_map_eq_of_source_homotopy A B C
    (rightKFlatResolutionObj A B C hC M).property (rightKFlatResolutionObj A B C hC M).property
    _ (𝟙 (bimoduleSourceProjectiveResolution A B C M).obj)
    (h.trans ((moduleToHomotopy A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ).map_id _).symm)
  exact he.trans ((congrArg (rightKFlatToDerived A B C).map
    (rightKFlatOfModuleMap_id A B C _ _)).trans ((rightKFlatToDerived A B C).map_id _))

lemma rightKFlatReplacementMap_comp (hC : localHomKFlat A C)
    {M N P : BimoduleCategory A B C} (f : M ⟶ N) (g : N ⟶ P) :
    (rightKFlatToDerived A B C).map (rightKFlatReplacementMap A B C hC (f ≫ g)) =
      (rightKFlatToDerived A B C).map (rightKFlatReplacementMap A B C hC f) ≫
        (rightKFlatToDerived A B C).map (rightKFlatReplacementMap A B C hC g) := by
  let R := bimoduleSourceProjectiveResolution A B C
  let F := (rightModuleBimoduleEquivalence A B C).inverse
  let K := moduleToHomotopy A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
  have h : K.map ((R M).lift (R P) (F.map (f ≫ g))) =
      K.map ((R M).lift (R N) (F.map f) ≫ (R N).lift (R P) (F.map g)) := by
    have he := congrArg (fun k => K.map ((R M).lift (R P) k)) (F.map_comp f g)
    exact he.trans (((R M).lift_comp (R N) (R P) (F.map f) (F.map g)).symm.trans
      (K.map_comp _ _).symm)
  have he := rightKFlat_map_eq_of_source_homotopy A B C
    (rightKFlatResolutionObj A B C hC M).property (rightKFlatResolutionObj A B C hC P).property
    _ _ h
  exact he.trans ((congrArg (rightKFlatToDerived A B C).map
    (rightKFlatOfModuleMap_comp A B C _ (rightKFlatResolutionObj A B C hC N).property _ _ _)).trans
      ((rightKFlatToDerived A B C).map_comp _ _))

def rightKFlatReplacementFunctor (hC : localHomKFlat A C) :
    BimoduleCategory A B C ⥤ DerivedRightKFlatBimoduleCategory A B C where
  obj M := (rightKFlatToDerived A B C).obj (rightKFlatResolutionObj A B C hC M)
  map f := (rightKFlatToDerived A B C).map (rightKFlatReplacementMap A B C hC f)
  map_id := rightKFlatReplacementMap_id A B C hC
  map_comp f g := rightKFlatReplacementMap_comp A B C hC f g

lemma rightKFlatReplacementFunctor_inverts (hC : localHomKFlat A C) :
    (BimoduleCategory.quasiIso A B C).IsInvertedBy (rightKFlatReplacementFunctor A B C hC) := by
  intro M N f hf
  apply Localization.inverts (rightKFlatToDerived A B C) (rightKFlatQuasiIso A B C)
  exact (rightModuleBimoduleEquivalence_quasiIso_iff A B C _).2
    ((bimoduleSourceProjectiveResolution A B C M).lift_quasiIso
      (bimoduleSourceProjectiveResolution A B C N) _
      ((rightModuleBimodule_inverse_quasiIso_iff A B C f).2 hf))

def derivedRightKFlatReplacement (hC : localHomKFlat A C) :
    DerivedBimoduleCategory A B C ⥤ DerivedRightKFlatBimoduleCategory A B C :=
  bimoduleDerivedLift A B C (rightKFlatReplacementFunctor A B C hC)
    (rightKFlatReplacementFunctor_inverts A B C hC)

lemma derivedRightKFlatReplacement_fac (hC : localHomKFlat A C) :
    bimoduleToDerived A B C ⋙ derivedRightKFlatReplacement A B C hC =
      rightKFlatReplacementFunctor A B C hC := bimoduleDerivedLift_fac A B C _ _

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end KFlatBimoduleReplacement

/-! ## KFlatBimoduleAugmentation（旧 SerrePositivity/DifferentialGraded/Derived/KFlatBimoduleAugmentation.lean） -/

/-! # K-flat部分圏の局所化内での置換増大射の自然性

## 概要
K-flat部分圏の局所化内での置換増大射の自然性。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/KFlatBimoduleGlobalAugmentation.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section KFlatBimoduleAugmentation
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

def rightKFlatAugmentation (hC : localHomKFlat A C) (M : RightKFlatBimoduleCategory A B C) :
    rightKFlatResolutionObj A B C hC M.obj ⟶ M :=
  ObjectProperty.homMk (bimoduleCanonicalSemifreeResolution A B C M.obj).π

lemma rightKFlat_inverse_rightRelativeKFlat (M : RightKFlatBimoduleCategory A B C) :
    Bimodule.rightRelativeKFlat A B C (BimoduleCategory.underlying A B C
      ((rightModuleBimoduleEquivalence A B C).functor.obj
        ((rightModuleBimoduleEquivalence A B C).inverse.obj M.obj))) :=
  Bimodule.rightRelativeKFlat_of_iso A B C
    ((rightModuleBimoduleEquivalence A B C).counitIso.app M.obj) M.property

lemma rightKFlatAugmentation_naturality (hC : localHomKFlat A C)
    {M N : RightKFlatBimoduleCategory A B C} (f : M ⟶ N) :
    (rightKFlatToDerived A B C).map (rightKFlatReplacementMap A B C hC f.hom) ≫
        (rightKFlatToDerived A B C).map (rightKFlatAugmentation A B C hC N) =
      (rightKFlatToDerived A B C).map (rightKFlatAugmentation A B C hC M) ≫
        (rightKFlatToDerived A B C).map f := by
  let H := rightModuleBimoduleEquivalence A B C
  let R := bimoduleSourceProjectiveResolution A B C
  let K := moduleToHomotopy A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
  let hN := rightKFlat_inverse_rightRelativeKFlat A B C N
  let ε : rightKFlatOfModule A B C (H.inverse.obj N.obj) hN ⟶ N :=
    ObjectProperty.homMk (H.counitIso.app N.obj).hom
  have hs : K.map ((R M.obj).lift (R N.obj) (H.inverse.map f.hom) ≫ (R N.obj).π) =
      K.map ((R M.obj).π ≫ H.inverse.map f.hom) :=
    (K.map_comp _ _).trans
      (((R M.obj).lift_fac (R N.obj) (H.inverse.map f.hom)).trans (K.map_comp _ _).symm)
  have he := rightKFlat_map_eq_of_source_homotopy A B C
    (rightKFlatResolutionObj A B C hC M.obj).property hN _ _ hs
  have hl : rightKFlatOfModuleMap A B C
        (rightKFlatResolutionObj A B C hC M.obj).property hN
        ((R M.obj).lift (R N.obj) (H.inverse.map f.hom) ≫ (R N.obj).π) ≫ ε =
      rightKFlatReplacementMap A B C hC f.hom ≫ rightKFlatAugmentation A B C hC N := by
    apply ObjectProperty.hom_ext
    change H.functor.map (_ ≫ _) ≫ (H.counitIso.app N.obj).hom =
      H.functor.map _ ≫ (H.functor.map (R N.obj).π ≫ (H.counitIso.app N.obj).hom)
    rw [H.functor.map_comp, Category.assoc]
  have hr : rightKFlatOfModuleMap A B C
        (rightKFlatResolutionObj A B C hC M.obj).property hN
        ((R M.obj).π ≫ H.inverse.map f.hom) ≫ ε =
      rightKFlatAugmentation A B C hC M ≫ f := by
    apply ObjectProperty.hom_ext
    change H.functor.map ((R M.obj).π ≫ H.inverse.map f.hom) ≫
      (H.counitIso.app N.obj).hom =
        (H.functor.map (R M.obj).π ≫ (H.counitIso.app M.obj).hom) ≫ f.hom
    rw [H.functor.map_comp, Category.assoc, Category.assoc]
    exact congrArg (fun k => H.functor.map (R M.obj).π ≫ k) (H.counitIso.hom.naturality f.hom)
  have hh := congrArg (fun k => k ≫ (rightKFlatToDerived A B C).map ε) he
  rw [← CategoryTheory.Functor.map_comp, hl, ← CategoryTheory.Functor.map_comp, hr] at hh
  exact ((rightKFlatToDerived A B C).map_comp _ _).symm.trans
    (hh.trans ((rightKFlatToDerived A B C).map_comp _ _))

def rightKFlatAugmentationIso (hC : localHomKFlat A C) :
    rightKFlatInclusion A B C ⋙ rightKFlatReplacementFunctor A B C hC ≅
      rightKFlatToDerived A B C :=
  NatIso.ofComponents
    (fun M => Localization.Construction.wIso (W := rightKFlatQuasiIso A B C)
      (rightKFlatAugmentation A B C hC M)
      (bimoduleCanonicalSemifreeResolution A B C M.obj).quasiIso)
    (fun f => rightKFlatAugmentation_naturality A B C hC f)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end KFlatBimoduleAugmentation

/-! ## KFlatBimoduleLeftRestriction（旧 SerrePositivity/DifferentialGraded/Derived/KFlatBimoduleLeftRestriction.lean） -/

/-! # 外側の左dg作用を制限しても右相対K-flat性を保つ

## 概要
外側の左dg作用を制限しても右相対K-flat性を保つ。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section KFlatBimoduleLeftRestriction
universe u v w z

noncomputable section
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (C : Type v) [DGCategory A C] [Small.{u} C]
  (E : Type w) [DGCategory A E] (D : Type z) [DGCategory A D] (F : DGFunctor A D E)

/-- 外側の左作用の制限は、各右加群を再選択するので右相対K-flat性を保つ。 -/
lemma leftRestriction_rightRelativeKFlat (Q : Bimodule A C E)
    (hQ : Bimodule.rightRelativeKFlat A C E Q) :
    Bimodule.rightRelativeKFlat A C D (Bimodule.leftRestriction A C E D F Q) :=
  fun d => hQ (F.obj d)

lemma leftRestriction_quasiIso {Q Q' : BimoduleCategory A C E} (q : Q ⟶ Q')
    (hq : BimoduleCategory.quasiIso A C E q) :
    BimoduleCategory.quasiIso A C D
      ((BimoduleCategory.middleLeftRestrictionFunctor A C E D F).map q) :=
  fun c d => hq c (F.obj d)

/-- 右K-flat部分圏上の、外側の左作用の実際の制限関手。 -/
def rightKFlatLeftRestriction :
    RightKFlatBimoduleCategory A C E ⥤ RightKFlatBimoduleCategory A C D where
  obj Q := ⟨(BimoduleCategory.middleLeftRestrictionFunctor A C E D F).obj Q.obj,
    leftRestriction_rightRelativeKFlat A C E D F _ Q.property⟩
  map q := ⟨(BimoduleCategory.middleLeftRestrictionFunctor A C E D F).map q.hom⟩
  map_id Q := by apply ObjectProperty.hom_ext; rfl
  map_comp q r := by apply ObjectProperty.hom_ext; rfl

lemma rightKFlatLeftRestriction_fac :
    rightKFlatLeftRestriction A C E D F ⋙ rightKFlatInclusion A C D =
      rightKFlatInclusion A C E ⋙ BimoduleCategory.middleLeftRestrictionFunctor A C E D F := rfl

lemma rightKFlatLeftRestriction_quasiIso
    {Q Q' : RightKFlatBimoduleCategory A C E} (q : Q ⟶ Q') (hq : rightKFlatQuasiIso A C E q) :
    rightKFlatQuasiIso A C D ((rightKFlatLeftRestriction A C E D F).map q) :=
  leftRestriction_quasiIso A C E D F q.hom hq

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end KFlatBimoduleLeftRestriction

/-! ## KFlatBimoduleGlobalAugmentation（旧 SerrePositivity/DifferentialGraded/Derived/KFlatBimoduleGlobalAugmentation.lean） -/

/-! # 全導来bimodule圏におけるK-flat置換増大射の自然性

## 概要
全導来bimodule圏におけるK-flat置換増大射の自然性。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleResolutionLift.lean、Derived/
KFlatBimoduleEquivalence.lean。固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section KFlatBimoduleGlobalAugmentation
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

omit [Small.{u} C] in
lemma rightKFlatDerivedInclusion_map_base {M N : RightKFlatBimoduleCategory A B C} (f : M ⟶ N) :
    (rightKFlatDerivedInclusion A B C).map ((rightKFlatToDerived A B C).map f) =
      (bimoduleToDerived A B C).map f.hom :=
  eq_of_heq (Functor.hcongr_hom (rightKFlatDerivedInclusion_fac A B C) f)

lemma rightKFlatGlobalAugmentation_naturality (hC : localHomKFlat A C)
    {M N : BimoduleCategory A B C} (f : M ⟶ N) :
    (rightKFlatDerivedInclusion A B C).map ((rightKFlatReplacementFunctor A B C hC).map f) ≫
        (bimoduleToDerived A B C).map (bimoduleCanonicalSemifreeResolution A B C N).π =
      (bimoduleToDerived A B C).map (bimoduleCanonicalSemifreeResolution A B C M).π ≫
        (bimoduleToDerived A B C).map f := by
  change (rightKFlatDerivedInclusion A B C).map
    ((rightKFlatToDerived A B C).map (rightKFlatReplacementMap A B C hC f)) ≫ _ = _
  rw [rightKFlatDerivedInclusion_map_base]
  let H := rightModuleBimoduleEquivalence A B C
  let R := bimoduleSourceProjectiveResolution A B C
  let K := moduleToHomotopy A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
  have hs : K.map ((R M).lift (R N) (H.inverse.map f) ≫ (R N).π) =
      K.map ((R M).π ≫ H.inverse.map f) :=
    (K.map_comp _ _).trans (((R M).lift_fac (R N) (H.inverse.map f)).trans (K.map_comp _ _).symm)
  have he := BimoduleSemifreeResolution.map_eq_of_source_homotopy _ _ hs
  have hl : H.functor.map ((R M).lift (R N) (H.inverse.map f) ≫ (R N).π) ≫
        (H.counitIso.app N).hom =
      (rightKFlatReplacementMap A B C hC f).hom ≫
        (bimoduleCanonicalSemifreeResolution A B C N).π := by
    change H.functor.map (_ ≫ _) ≫ (H.counitIso.app N).hom =
      H.functor.map _ ≫ (H.functor.map (R N).π ≫ (H.counitIso.app N).hom)
    rw [H.functor.map_comp, Category.assoc]
  have hr : H.functor.map ((R M).π ≫ H.inverse.map f) ≫ (H.counitIso.app N).hom =
      (bimoduleCanonicalSemifreeResolution A B C M).π ≫ f := by
    change H.functor.map ((R M).π ≫ H.inverse.map f) ≫ (H.counitIso.app N).hom =
      (H.functor.map (R M).π ≫ (H.counitIso.app M).hom) ≫ f
    rw [H.functor.map_comp, Category.assoc, Category.assoc]
    exact congrArg (fun k => H.functor.map (R M).π ≫ k) (H.counitIso.hom.naturality f)
  have hh := congrArg (fun k => k ≫ (bimoduleToDerived A B C).map (H.counitIso.app N).hom) he
  rw [← CategoryTheory.Functor.map_comp, hl, ← CategoryTheory.Functor.map_comp, hr] at hh
  exact ((bimoduleToDerived A B C).map_comp _ _).symm.trans
    (hh.trans ((bimoduleToDerived A B C).map_comp _ _))

def rightKFlatGlobalAugmentationIso (hC : localHomKFlat A C) :
    rightKFlatReplacementFunctor A B C hC ⋙ rightKFlatDerivedInclusion A B C ≅
      bimoduleToDerived A B C :=
  NatIso.ofComponents
    (fun M => bimoduleDerivedIso A B C (bimoduleCanonicalSemifreeResolution A B C M).π
      (bimoduleCanonicalSemifreeResolution A B C M).quasiIso)
    (fun f => rightKFlatGlobalAugmentation_naturality A B C hC f)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end KFlatBimoduleGlobalAugmentation

/-! ## KFlatBimoduleEquivalence（旧 SerrePositivity/DifferentialGraded/Derived/KFlatBimoduleEquivalence.lean） -/

/-! # K-flat部分圏の準同型局所化と全導来bimodule圏の同値

## 概要
K-flat部分圏の準同型局所化と全導来bimodule圏の同値。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleComposition.lean。固定dg圏上の導来tensor・
Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section KFlatBimoduleEquivalence
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

instance derivedRightKFlatReplacement_lifting (hC : localHomKFlat A C) :
    Localization.Lifting (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
      (rightKFlatReplacementFunctor A B C hC) (derivedRightKFlatReplacement A B C hC) :=
  ⟨eqToIso (derivedRightKFlatReplacement_fac A B C hC)⟩

def rightKFlatCompositeFacIso (hC : localHomKFlat A C) :
    rightKFlatToDerived A B C ⋙
        (rightKFlatDerivedInclusion A B C ⋙ derivedRightKFlatReplacement A B C hC) ≅
      rightKFlatInclusion A B C ⋙ rightKFlatReplacementFunctor A B C hC :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eqToIso (rightKFlatDerivedInclusion_fac A B C))
      (derivedRightKFlatReplacement A B C hC) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (rightKFlatInclusion A B C)
      (eqToIso (derivedRightKFlatReplacement_fac A B C hC))

instance rightKFlatComposite_lifting (hC : localHomKFlat A C) :
    Localization.Lifting (rightKFlatToDerived A B C) (rightKFlatQuasiIso A B C)
      (rightKFlatInclusion A B C ⋙ rightKFlatReplacementFunctor A B C hC)
      (rightKFlatDerivedInclusion A B C ⋙ derivedRightKFlatReplacement A B C hC) :=
  ⟨rightKFlatCompositeFacIso A B C hC⟩

def rightKFlatReplacementUnitIso (hC : localHomKFlat A C) :
    rightKFlatDerivedInclusion A B C ⋙ derivedRightKFlatReplacement A B C hC ≅
      𝟭 (DerivedRightKFlatBimoduleCategory A B C) :=
  Localization.liftNatIso (rightKFlatToDerived A B C) (rightKFlatQuasiIso A B C)
    (rightKFlatInclusion A B C ⋙ rightKFlatReplacementFunctor A B C hC)
    (rightKFlatToDerived A B C)
    (rightKFlatDerivedInclusion A B C ⋙ derivedRightKFlatReplacement A B C hC) (𝟭 _)
    (rightKFlatAugmentationIso A B C hC)

def rightKFlatReplacementCounitIso (hC : localHomKFlat A C) :
    derivedRightKFlatReplacement A B C hC ⋙ rightKFlatDerivedInclusion A B C ≅
      𝟭 (DerivedBimoduleCategory A B C) :=
  Localization.liftNatIso (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
    (rightKFlatReplacementFunctor A B C hC ⋙ rightKFlatDerivedInclusion A B C)
    (bimoduleToDerived A B C)
    (derivedRightKFlatReplacement A B C hC ⋙ rightKFlatDerivedInclusion A B C) (𝟭 _)
    (rightKFlatGlobalAugmentationIso A B C hC)

/-- Mathlibのadjointificationで三角恒等式も備えた圏同値を構成する。 -/
def rightKFlatDerivedEquivalence (hC : localHomKFlat A C) :
    DerivedRightKFlatBimoduleCategory A B C ≌ DerivedBimoduleCategory A B C :=
  CategoryTheory.Equivalence.mk (rightKFlatDerivedInclusion A B C)
    (derivedRightKFlatReplacement A B C hC)
    (rightKFlatReplacementUnitIso A B C hC).symm (rightKFlatReplacementCounitIso A B C hC)

lemma rightKFlatDerivedInclusion_isEquivalence (hC : localHomKFlat A C) :
    (rightKFlatDerivedInclusion A B C).IsEquivalence :=
  (rightKFlatDerivedEquivalence A B C hC).isEquivalence_functor

def rightKFlatDerivedInclusion_fullyFaithful (hC : localHomKFlat A C) :
    (rightKFlatDerivedInclusion A B C).FullyFaithful :=
  (rightKFlatDerivedEquivalence A B C hC).fullyFaithfulFunctor

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end KFlatBimoduleEquivalence
