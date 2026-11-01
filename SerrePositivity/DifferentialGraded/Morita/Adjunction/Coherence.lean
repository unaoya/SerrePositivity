module

public import SerrePositivity.DifferentialGraded.Morita.U16a
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Unique
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtension.PerfectSquares
public import SerrePositivity.DifferentialGraded.Morita.Perfect
public import SerrePositivity.DifferentialGraded.Morita.CriterionDerived

/-!
# Morita.Adjunction.Coherence

## 概要
実際の右随伴の正方形・合成・係数変更と Perf 逆関手の比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

universe u u' v w v' w' z t z'

/-! ## AdjunctionSquare（旧 SerrePositivity/DifferentialGraded/Morita/AdjunctionSquare.lean） -/

/-! # Morita作用の正方形から実際の右随伴の正方形へ

## 概要
二つのkernel作用が同値なら、左作用の比較正方形を実際の一般右随伴の比較へ運ぶ。

## 方針
左作用の正方形の逆、元の実際の余単位、変更後の実際の単位から自然同型を構成する。

## 規約と注意
係数環・対象宇宙を独立に保つ。左右の作用の同値性は三条件Morita判定から供給できる。
左作用の比較を入力から新たに証明したとはしない。係数変更の未完図式を代用しない。

## 使われ方
U16dの係数変更比較を、U16cで同定した実際の右随伴側へ接続する。
-/

@[expose] public section AdjunctionSquare

noncomputable section
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (A' : Type u') [CommRing A']
  (D' : Type v') [DGCategory A' D'] [Small.{u'} D']
  (E' : Type w') [DGCategory A' E'] [Small.{u'} E']
  (K : Kernel A D E) (K' : Kernel A' D' E')
  [(kernelDerivedTensor A D E K).IsEquivalence]
  [(kernelDerivedTensor A' D' E' K').IsEquivalence]
  (S : DerivedModuleCategory A D ⥤ DerivedModuleCategory A' D')
  (T : DerivedModuleCategory A E ⥤ DerivedModuleCategory A' E')
  (e : kernelDerivedTensor A D E K ⋙ T ≅ S ⋙ kernelDerivedTensor A' D' E' K')

/-- 実際の両随伴で転置した、右随伴側の比較自然同型。 -/
def kernelRightAdjointSquareIso :
    kernelDerivedHom A D E K ⋙ S ≅ T ⋙ kernelDerivedHom A' D' E' K' := by
  have : IsIso (kernelDerivedUnit A' D' E' K') := by
    change IsIso (kernelDerivedAdjunction A' D' E' K').unit
    infer_instance
  have : IsIso (kernelDerivedCounit A D E K) := by
    change IsIso (kernelDerivedAdjunction A D E K).counit
    infer_instance
  let R := kernelDerivedHom A D E K
  let R' := kernelDerivedHom A' D' E' K'
  let L := kernelDerivedTensor A D E K
  let L' := kernelDerivedTensor A' D' E' K'
  let η := asIso (kernelDerivedUnit A' D' E' K')
  let ε := asIso (kernelDerivedCounit A D E K)
  exact (rightUnitor (R ⋙ S)).symm ≪≫ isoWhiskerLeft (R ⋙ S) η ≪≫
    (associator (R ⋙ S) L' R').symm ≪≫
    isoWhiskerRight (associator R S L') R' ≪≫
    isoWhiskerRight (isoWhiskerLeft R e.symm) R' ≪≫
    isoWhiskerRight (associator R L T).symm R' ≪≫
    isoWhiskerRight (isoWhiskerRight ε T) R' ≪≫
    isoWhiskerRight (leftUnitor T) R'

/-- 比較の成分は、変更後の実際の単位と元の実際の余単位で計算する。 -/
lemma kernelRightAdjointSquareIso_hom_app (Y : DerivedModuleCategory A E) :
    (kernelRightAdjointSquareIso A D E A' D' E' K K' S T e).hom.app Y =
      (kernelDerivedUnit A' D' E' K').app (S.obj ((kernelDerivedHom A D E K).obj Y)) ≫
        (kernelDerivedHom A' D' E' K').map (e.inv.app ((kernelDerivedHom A D E K).obj Y)) ≫
        (kernelDerivedHom A' D' E' K').map (T.map ((kernelDerivedCounit A D E K).app Y)) := by
  dsimp only [kernelRightAdjointSquareIso]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app, rightUnitor_inv_app,
    associator_hom_app, associator_inv_app, leftUnitor_hom_app, asIso_hom,
    CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.id_comp, Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

/-- 右随伴の正方形は、実際の余単位で元の左作用の比較に戻る。 -/
lemma kernelRightAdjointSquareIso_counit (Y : DerivedModuleCategory A E) :
    (kernelDerivedTensor A' D' E' K').map
        ((kernelRightAdjointSquareIso A D E A' D' E' K K' S T e).hom.app Y) ≫
      (kernelDerivedCounit A' D' E' K').app (T.obj Y) =
    e.inv.app ((kernelDerivedHom A D E K).obj Y) ≫
      T.map ((kernelDerivedCounit A D E K).app Y) := by
  let g := e.inv.app ((kernelDerivedHom A D E K).obj Y) ≫
    T.map ((kernelDerivedCounit A D E K).app Y)
  have hn := (kernelDerivedCounit A' D' E' K').naturality g
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [kernelRightAdjointSquareIso_hom_app, ← Functor.map_comp,
    Functor.map_comp, Category.assoc]
  erw [hn]
  rw [← Category.assoc]
  erw [kernelDerived_left_triangle A' D' E' K'
    (S.obj ((kernelDerivedHom A D E K).obj Y)), Category.id_comp]

/-- 右随伴の比較は、係数変更の両側の実際の単位にも整合する。 -/
lemma kernelRightAdjointSquareIso_unit (X : DerivedModuleCategory A D) :
    S.map ((kernelDerivedUnit A D E K).app X) ≫
        (kernelRightAdjointSquareIso A D E A' D' E' K K' S T e).hom.app
          ((kernelDerivedTensor A D E K).obj X) =
      (kernelDerivedUnit A' D' E' K').app (S.obj X) ≫
        (kernelDerivedHom A' D' E' K').map (e.inv.app X) := by
  let η := (kernelDerivedUnit A D E K).app X
  let ε := (kernelDerivedCounit A D E K).app ((kernelDerivedTensor A D E K).obj X)
  have hu := (kernelDerivedUnit A' D' E' K').naturality (S.map η)
  simp only [Functor.id_map, Functor.comp_map] at hu
  have he := e.inv.naturality η
  simp only [Functor.comp_map] at he
  have hg : (kernelDerivedTensor A' D' E' K').map (S.map η) ≫
      (e.inv.app ((kernelDerivedHom A D E K).obj ((kernelDerivedTensor A D E K).obj X)) ≫
        T.map ε) = e.inv.app X := by
    rw [← Category.assoc]
    erw [he]
    rw [Category.assoc, ← T.map_comp]
    erw [kernelDerived_left_triangle A D E K X,
      CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  rw [kernelRightAdjointSquareIso_hom_app, ← Category.assoc]
  erw [hu]
  simp only [Category.assoc]
  slice_lhs 2 4 => rw [← Functor.map_comp, ← Functor.map_comp]
  erw [hg]
  rfl

/-- 恒等な左作用正方形は、実際の右随伴の恒等正方形へ運ばれる。 -/
lemma kernelRightAdjointSquareIso_identity :
    kernelRightAdjointSquareIso A D E A D E K K (𝟭 _) (𝟭 _)
        (rightUnitor (kernelDerivedTensor A D E K) ≪≫
          (leftUnitor (kernelDerivedTensor A D E K)).symm) =
      rightUnitor (kernelDerivedHom A D E K) ≪≫
        (leftUnitor (kernelDerivedHom A D E K)).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext Y
  rw [kernelRightAdjointSquareIso_hom_app]
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, rightUnitor_inv_app,
    leftUnitor_hom_app, Iso.trans_hom, Iso.symm_hom, rightUnitor_hom_app,
    leftUnitor_inv_app, Functor.id_map]
  erw [Category.id_comp, Category.id_comp, CategoryTheory.Functor.map_id, Category.id_comp]
  exact kernelDerived_right_triangle A D E K Y

end SerrePositivity.DifferentialGraded.Morita
end

end AdjunctionSquare

/-! ## AdjunctionCoherence（旧 SerrePositivity/DifferentialGraded/Morita/AdjunctionCoherence.lean） -/

/-! # 恒等・合成kernelの実際の右随伴の比較

## 概要
一般右随伴を恒等kernelと合成kernelで計算し、実際のunit/counitの比較を公開する。

## 方針
既存kernelIdentityIso・kernelCompositionIsoで随伴を移し、右随伴の一意性を適用する。

## 規約と注意
kernelのMorita性・列の射影性は不要。合成には始域DのlocalHomKFlatだけを保持する。

## 使われ方
U16の実際の一般右随伴による恒等・逆順合成の計算と、Morita逆関手の合成比較。
-/

@[expose] public section AdjunctionCoherence

noncomputable section
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 恒等作用の実際の比較から作った、恒等関手を右随伴とする随伴。 -/
def kernelIdentityRightAdjunction :
    kernelDerivedTensor A D D (kernelIdentity A D) ⊣ 𝟭 (DerivedModuleCategory A D) :=
  Adjunction.id.ofNatIsoLeft (kernelIdentityIso A D).symm

/-- 恒等kernelの実際の一般右随伴は恒等関手に自然同型。 -/
def kernelDerivedHomIdentityIso :
    kernelDerivedHom A D D (kernelIdentity A D) ≅ 𝟭 (DerivedModuleCategory A D) :=
  Adjunction.rightAdjointUniq (kernelDerivedAdjunction A D D (kernelIdentity A D))
    (kernelIdentityRightAdjunction A D)

/-- 恒等kernelの右随伴比較は、実際の単位と恒等作用比較を接続する。 -/
lemma kernelDerivedHomIdentityIso_unit (X : DerivedModuleCategory A D) :
    (kernelDerivedUnit A D D (kernelIdentity A D)).app X ≫
      (kernelDerivedHomIdentityIso A D).hom.app
        ((kernelDerivedTensor A D D (kernelIdentity A D)).obj X) =
    (kernelIdentityIso A D).inv.app X := by
  have h := Adjunction.unit_rightAdjointUniq_hom_app
    (kernelDerivedAdjunction A D D (kernelIdentity A D)) (kernelIdentityRightAdjunction A D) X
  change _ = 𝟙 _ ≫ (𝟭 (DerivedModuleCategory A D)).map ((kernelIdentityIso A D).inv.app X) at h
  simpa only [Functor.id_map, Functor.id_obj, Category.id_comp, kernelDerivedUnit,
    kernelDerivedHomIdentityIso] using h

/-- 恒等kernelの右随伴比較は、実際の余単位と恒等作用比較を接続する。 -/
lemma kernelDerivedHomIdentityIso_counit (Y : DerivedModuleCategory A D) :
    (kernelDerivedTensor A D D (kernelIdentity A D)).map
        ((kernelDerivedHomIdentityIso A D).hom.app Y) ≫
      (kernelIdentityIso A D).hom.app Y =
    (kernelDerivedCounit A D D (kernelIdentity A D)).app Y := by
  have h := Adjunction.rightAdjointUniq_hom_app_counit
    (kernelDerivedAdjunction A D D (kernelIdentity A D)) (kernelIdentityRightAdjunction A D) Y
  change _ ≫ ((kernelIdentityIso A D).hom.app Y ≫ 𝟙 _) = _ at h
  simpa only [Category.comp_id, kernelDerivedCounit, kernelDerivedHomIdentityIso] using h

variable (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]
  (hD : localHomKFlat A D) (P : Kernel A D E) (Q : Kernel A E F)

/-- 合成kernel作用に、二つの実際の一般右随伴の逆順合成を随伴させる。 -/
def kernelCompositionRightAdjunction :
    kernelDerivedTensor A D F (kernelCompose A D E F hD P Q) ⊣
      kernelDerivedHom A E F Q ⋙ kernelDerivedHom A D E P :=
  ((kernelDerivedAdjunction A D E P).comp (kernelDerivedAdjunction A E F Q)).ofNatIsoLeft
    (kernelCompositionIso A D E F hD P Q)

/-- 移した合成随伴の単位は元の二つの実際の単位で計算する。 -/
lemma kernelCompositionRightAdjunction_unit_app (X : DerivedModuleCategory A D) :
    (kernelCompositionRightAdjunction A D E F hD P Q).unit.app X =
      (kernelDerivedUnit A D E P).app X ≫
        (kernelDerivedHom A D E P).map
          ((kernelDerivedUnit A E F Q).app ((kernelDerivedTensor A D E P).obj X)) ≫
        (kernelDerivedHom A D E P).map
          ((kernelDerivedHom A E F Q).map ((kernelCompositionIso A D E F hD P Q).hom.app X)) := by
  change ((kernelDerivedAdjunction A D E P).comp (kernelDerivedAdjunction A E F Q)).unit.app X ≫
    (kernelDerivedHom A D E P).map
      ((kernelDerivedHom A E F Q).map ((kernelCompositionIso A D E F hD P Q).hom.app X)) = _
  rw [Adjunction.comp_unit_app]
  simp only [kernelDerivedUnit, Category.assoc]

/-- 移した合成随伴の余単位は元の二つの実際の余単位で計算する。 -/
lemma kernelCompositionRightAdjunction_counit_app (Y : DerivedModuleCategory A F) :
    (kernelCompositionRightAdjunction A D E F hD P Q).counit.app Y =
      (kernelCompositionIso A D E F hD P Q).inv.app
          ((kernelDerivedHom A D E P).obj ((kernelDerivedHom A E F Q).obj Y)) ≫
        (kernelDerivedTensor A E F Q).map
          ((kernelDerivedCounit A D E P).app ((kernelDerivedHom A E F Q).obj Y)) ≫
        (kernelDerivedCounit A E F Q).app Y := by
  change (kernelCompositionIso A D E F hD P Q).inv.app _ ≫
    ((kernelDerivedAdjunction A D E P).comp (kernelDerivedAdjunction A E F Q)).counit.app Y = _
  rw [Adjunction.comp_counit_app]
  rfl

/-- 合成kernelの実際の一般右随伴は、二つの一般右随伴の逆順合成に自然同型。 -/
def kernelDerivedHomCompositionIso :
    kernelDerivedHom A D F (kernelCompose A D E F hD P Q) ≅
      kernelDerivedHom A E F Q ⋙ kernelDerivedHom A D E P :=
  Adjunction.rightAdjointUniq
    (kernelDerivedAdjunction A D F (kernelCompose A D E F hD P Q))
    (kernelCompositionRightAdjunction A D E F hD P Q)

/-- 合成kernelの右随伴比較は、元の二つの実際の単位との図式を満たす。 -/
lemma kernelDerivedHomCompositionIso_unit (X : DerivedModuleCategory A D) :
    (kernelDerivedUnit A D F (kernelCompose A D E F hD P Q)).app X ≫
      (kernelDerivedHomCompositionIso A D E F hD P Q).hom.app
        ((kernelDerivedTensor A D F (kernelCompose A D E F hD P Q)).obj X) =
    (kernelDerivedUnit A D E P).app X ≫
      (kernelDerivedHom A D E P).map
        ((kernelDerivedUnit A E F Q).app ((kernelDerivedTensor A D E P).obj X)) ≫
      (kernelDerivedHom A D E P).map
        ((kernelDerivedHom A E F Q).map ((kernelCompositionIso A D E F hD P Q).hom.app X)) :=
  (Adjunction.unit_rightAdjointUniq_hom_app
    (kernelDerivedAdjunction A D F (kernelCompose A D E F hD P Q))
    (kernelCompositionRightAdjunction A D E F hD P Q) X).trans
      (kernelCompositionRightAdjunction_unit_app A D E F hD P Q X)

/-- 合成kernelの右随伴比較は、元の二つの実際の余単位との図式を満たす。 -/
lemma kernelDerivedHomCompositionIso_counit (Y : DerivedModuleCategory A F) :
    (kernelDerivedTensor A D F (kernelCompose A D E F hD P Q)).map
        ((kernelDerivedHomCompositionIso A D E F hD P Q).hom.app Y) ≫
      (kernelCompositionIso A D E F hD P Q).inv.app
          ((kernelDerivedHom A D E P).obj ((kernelDerivedHom A E F Q).obj Y)) ≫
      (kernelDerivedTensor A E F Q).map
        ((kernelDerivedCounit A D E P).app ((kernelDerivedHom A E F Q).obj Y)) ≫
      (kernelDerivedCounit A E F Q).app Y =
    (kernelDerivedCounit A D F (kernelCompose A D E F hD P Q)).app Y := by
  have h := Adjunction.rightAdjointUniq_hom_app_counit
    (kernelDerivedAdjunction A D F (kernelCompose A D E F hD P Q))
    (kernelCompositionRightAdjunction A D E F hD P Q) Y
  rw [kernelCompositionRightAdjunction_counit_app] at h
  exact h

end SerrePositivity.DifferentialGraded.Morita
end

end AdjunctionCoherence

/-! ## AdjunctionScalarExtension（旧 SerrePositivity/DifferentialGraded/Morita/AdjunctionScalarExtension.lean） -/

/-! # 局所化kernel係数変更と実際のMorita右随伴

## 概要
既存の条件付き係数変更正方形を、元と変更後の実際の一般右随伴へ接続する。

## 方針
scalarKernelLocalizedDerivedSquareを、実際の単位・余単位による右随伴正方形へ転置する。

## 規約と注意
両kernel作用の同値性、通常代表、hα・hAug・hP'を保持する。
係数変更後のMorita性を無条件に結論しない。未完のU12f成分同定・kernel合成比較は代用しない。

## 使われ方
U16cの一般右随伴を、U16dの実際の局所化係数変更正方形に適用する入口。
-/

@[expose] public section AdjunctionScalarExtension

noncomputable section
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (P : BimoduleCategory A E D)
  (hα : IsIso ((scalarKernelDerivedExtensionAugmentation φ D E).app P))
  (hAug : ∀ M : ModuleCategory A D,
    IsIso ((derivedExtensionAugmentation φ E).app
      ((kernelTensor A D E (BimoduleCategory.underlying A E D P)).onClosed.obj
        (moduleCanonicalProjectiveResolution A D M).obj)))
  (hP' : ∀ M : ModuleCategory A D,
    moduleRelativeKFlat A' (DGBaseChange φ D)
      (rightModule φ D (ForgetEnrichment.to (Complex A)
        (moduleCanonicalProjectiveResolution A D M).obj)))
variable [(kernelDerivedTensor A D E ((bimoduleToDerived A E D).obj P)).IsEquivalence]
  [(kernelDerivedTensor A' (DGBaseChange φ D) (DGBaseChange φ E)
    ((scalarKernelDerivedExtension φ D E).obj ((bimoduleToDerived A E D).obj P))).IsEquivalence]

/-- 実際の局所化kernelの係数変更正方形から得る、一般右随伴側の比較。 -/
def kernelRightAdjointLocalizedBaseChangeIso :
    kernelDerivedHom A D E ((bimoduleToDerived A E D).obj P) ⋙ derivedExtension φ D ≅
      derivedExtension φ E ⋙
        kernelDerivedHom A' (DGBaseChange φ D) (DGBaseChange φ E)
          ((scalarKernelDerivedExtension φ D E).obj ((bimoduleToDerived A E D).obj P)) :=
  kernelRightAdjointSquareIso A D E A' (DGBaseChange φ D) (DGBaseChange φ E)
    ((bimoduleToDerived A E D).obj P)
    ((scalarKernelDerivedExtension φ D E).obj ((bimoduleToDerived A E D).obj P))
    (derivedExtension φ D) (derivedExtension φ E)
    (scalarKernelLocalizedDerivedSquare φ D E P hα hAug hP')

/-- 係数変更の右随伴比較は、実際の余単位で既存の左作用正方形へ戻る。 -/
lemma kernelRightAdjointLocalizedBaseChangeIso_counit (Y : DerivedModuleCategory A E) :
    (kernelDerivedTensor A' (DGBaseChange φ D) (DGBaseChange φ E)
      ((scalarKernelDerivedExtension φ D E).obj ((bimoduleToDerived A E D).obj P))).map
        ((kernelRightAdjointLocalizedBaseChangeIso φ D E P hα hAug hP').hom.app Y) ≫
      (kernelDerivedCounit A' (DGBaseChange φ D) (DGBaseChange φ E)
        ((scalarKernelDerivedExtension φ D E).obj ((bimoduleToDerived A E D).obj P))).app
        ((derivedExtension φ E).obj Y) =
    (scalarKernelLocalizedDerivedSquare φ D E P hα hAug hP').inv.app
        ((kernelDerivedHom A D E ((bimoduleToDerived A E D).obj P)).obj Y) ≫
      (derivedExtension φ E).map
        ((kernelDerivedCounit A D E ((bimoduleToDerived A E D).obj P)).app Y) :=
  kernelRightAdjointSquareIso_counit A D E A' (DGBaseChange φ D) (DGBaseChange φ E)
    ((bimoduleToDerived A E D).obj P)
    ((scalarKernelDerivedExtension φ D E).obj ((bimoduleToDerived A E D).obj P))
    (derivedExtension φ D) (derivedExtension φ E)
    (scalarKernelLocalizedDerivedSquare φ D E P hα hAug hP') Y

end SerrePositivity.DifferentialGraded.Morita
end

end AdjunctionScalarExtension

/-! ## CoherencePerfectUnit（旧 SerrePositivity/DifferentialGraded/Morita/CoherencePerfectUnit.lean） -/

/-! # 実際のPerf作用比較の両単位coherence

## 概要
受入済みの主導来作用の両単位図式を、別担当の既存Perf作用比較そのものへ移す。

## 方針
Perf包含の忠実性と既存制限の成分式を使い、元の公開図式に帰着する。

## 規約と注意
公開比較の定義を変更しない。必要な局所Hom条件と列のperfect性は保持する。

## 使われ方
U16dの既存Perf比較にU16aの作用coherenceを供給するアダプタ。
-/

@[expose] public section CoherencePerfectUnit

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (hD : localHomKFlat A D)
  (P : Kernel A D E) (hP : kernelColumnsPerfect A D E P)

/-- 既存の実際のPerf合成比較と右単位子は整合する。 -/
lemma perfectKernelCompositionIso_rightUnit :
    (perfectKernelCompositionIso A D D E hD (kernelIdentity A D) P
      (kernelIdentity_columnsPerfect A D) hP).hom ≫
      perfectDerivedKernelMap A D E
        (kernelCompose_columnsPerfect_of_columns A D D E hD (kernelIdentity A D) P
          (kernelIdentity_columnsPerfect A D) hP) hP
        ((derivedBimoduleRightUnitIso A E D hD).hom.app P) =
    whiskerRight (perfectDerivedKernelIdentityIso A D).hom (perfectDerivedKernelAction A D E P hP) ≫
      (Functor.leftUnitor (perfectDerivedKernelAction A D E P hP)).hom := by
  apply NatTrans.ext
  funext X
  apply (modulePerfect A E).hom_ext
  have h := NatTrans.congr_app (kernelCompositionIso_rightUnit A D E hD P) X.obj
  simp only [NatTrans.comp_app, whiskerRight_app, Functor.leftUnitor_hom_app] at h
  simp only [NatTrans.comp_app, whiskerRight_app, Functor.leftUnitor_hom_app,
    perfectKernelCompositionIso, perfectDerivedKernelCompositionIso, perfectFunctorCompositionIso,
    perfectFunctorIso, perfectDerivedKernelIdentityIso, perfectFunctorIdentityIso,
    Iso.trans_hom, NatIso.ofComponents, ObjectProperty.isoMk, Iso.refl_hom, NatTrans.id_app]
  change (𝟙 _ ≫ (kernelCompositionIso A D D E hD (kernelIdentity A D) P).hom.app X.obj) ≫
      ((kernelDerivedTensorFunctor A D E).map
        ((derivedBimoduleRightUnitIso A E D hD).hom.app P)).app X.obj =
    (kernelDerivedTensor A D E P).map ((kernelIdentityIso A D).hom.app X.obj ≫ 𝟙 _) ≫ 𝟙 _
  erw [Category.comp_id] at h
  simpa only [Category.id_comp, Category.comp_id] using h

/-- 既存の実際のPerf合成比較と左単位子は整合する。 -/
lemma perfectKernelCompositionIso_leftUnit (hE : localHomKFlat A E) :
    (perfectKernelCompositionIso A D E E hD P (kernelIdentity A E)
      hP (kernelIdentity_columnsPerfect A E)).hom ≫
      perfectDerivedKernelMap A D E
        (kernelCompose_columnsPerfect_of_columns A D E E hD P (kernelIdentity A E)
          hP (kernelIdentity_columnsPerfect A E)) hP
        ((derivedBimoduleLeftUnitIso A E D hD).hom.app P) =
    whiskerLeft (perfectDerivedKernelAction A D E P hP) (perfectDerivedKernelIdentityIso A E).hom ≫
      (Functor.rightUnitor (perfectDerivedKernelAction A D E P hP)).hom := by
  apply NatTrans.ext
  funext X
  apply (modulePerfect A E).hom_ext
  have h := NatTrans.congr_app (kernelCompositionIso_leftUnit A D E hD hE P) X.obj
  simp only [NatTrans.comp_app, whiskerLeft_app, Functor.rightUnitor_hom_app] at h
  simp only [NatTrans.comp_app, whiskerLeft_app, Functor.rightUnitor_hom_app,
    perfectKernelCompositionIso, perfectDerivedKernelCompositionIso, perfectFunctorCompositionIso,
    perfectFunctorIso, perfectDerivedKernelIdentityIso, perfectFunctorIdentityIso,
    Iso.trans_hom, NatIso.ofComponents, ObjectProperty.isoMk, Iso.refl_hom, NatTrans.id_app]
  change (𝟙 _ ≫ (kernelCompositionIso A D E E hD P (kernelIdentity A E)).hom.app X.obj) ≫
      ((kernelDerivedTensorFunctor A D E).map
        ((derivedBimoduleLeftUnitIso A E D hD).hom.app P)).app X.obj =
    ((kernelIdentityIso A E).hom.app ((kernelDerivedTensor A D E P).obj X.obj) ≫ 𝟙 _) ≫ 𝟙 _
  erw [Category.comp_id] at h
  simpa only [Category.id_comp, Category.comp_id] using h

end SerrePositivity.DifferentialGraded.Morita
end

end CoherencePerfectUnit

/-! ## CoherencePerfectAssociator（旧 SerrePositivity/DifferentialGraded/Morita/CoherencePerfectAssociator.lean） -/

/-! # 実際のPerf作用比較の結合coherence

## 概要
別担当の実際のPerf合成比較について、三kernelの結合図式を証明する。

## 方針
包含の忠実性で主導来射へ戻し、受入済みkernelCompositionIso_associatorを適用する。

## 規約と注意
合成kernelの列のperfect性は既存の定理から供給し、追加仮定として受け取らない。

## 使われ方
U16dのPerf作用coherenceへの接続。係数変更の残接続とは区別する。
-/

@[expose] public section CoherencePerfectAssociator

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]
  (G : Type t) [DGCategory A G] [Small.{u} G]
  (hD : localHomKFlat A D) (hE : localHomKFlat A E)
  (P : Kernel A D E) (Q : Kernel A E F) (R : Kernel A F G)
  (hP : kernelColumnsPerfect A D E P) (hQ : kernelColumnsPerfect A E F Q)
  (hR : kernelColumnsPerfect A F G R)

/-- 既存の実際のPerf合成比較は、主導来kernel結合子と整合する。 -/
theorem perfectKernelCompositionIso_associator :
    let hPQ := kernelCompose_columnsPerfect_of_columns A D E F hD P Q hP hQ
    let hQR := kernelCompose_columnsPerfect_of_columns A E F G hE Q R hQ hR
    whiskerRight (perfectKernelCompositionIso A D E F hD P Q hP hQ).hom
        (perfectDerivedKernelAction A F G R hR) ≫
      (perfectKernelCompositionIso A D F G hD (kernelCompose A D E F hD P Q) R hPQ hR).hom =
    (Functor.associator (perfectDerivedKernelAction A D E P hP)
      (perfectDerivedKernelAction A E F Q hQ) (perfectDerivedKernelAction A F G R hR)).hom ≫
      whiskerLeft (perfectDerivedKernelAction A D E P hP)
        (perfectKernelCompositionIso A E F G hE Q R hQ hR).hom ≫
      (perfectKernelCompositionIso A D E G hD P (kernelCompose A E F G hE Q R) hP hQR).hom ≫
      perfectDerivedKernelMap A D G
        (kernelCompose_columnsPerfect_of_columns A D E G hD P (kernelCompose A E F G hE Q R) hP hQR)
        (kernelCompose_columnsPerfect_of_columns A D F G hD (kernelCompose A D E F hD P Q) R hPQ hR)
        (kernelAssociatorIso A D E F G hD hE P Q R).hom := by
  dsimp only
  apply NatTrans.ext
  funext X
  apply (modulePerfect A G).hom_ext
  have h := NatTrans.congr_app (kernelCompositionIso_associator A D E F G hD hE P Q R) X.obj
  dsimp only [kernelAssociatorLeftPath, kernelAssociatorRightPath] at h
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    Functor.associator_hom_app] at h
  erw [Category.id_comp] at h
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, Functor.associator_hom_app,
    perfectKernelCompositionIso, perfectDerivedKernelCompositionIso, perfectFunctorCompositionIso,
    perfectFunctorIso, Iso.trans_hom, NatIso.ofComponents, ObjectProperty.isoMk, Iso.refl_hom]
  change (kernelDerivedTensor A F G R).map
      (𝟙 _ ≫ (kernelCompositionIso A D E F hD P Q).hom.app X.obj) ≫
      (𝟙 _ ≫ (kernelCompositionIso A D F G hD
        (kernelCompose A D E F hD P Q) R).hom.app X.obj) =
    𝟙 _ ≫ (𝟙 _ ≫ (kernelCompositionIso A E F G hE Q R).hom.app
      ((kernelDerivedTensor A D E P).obj X.obj)) ≫
      (𝟙 _ ≫ (kernelCompositionIso A D E G hD P (kernelCompose A E F G hE Q R)).hom.app X.obj) ≫
      ((kernelDerivedTensorFunctor A D G).map
        (kernelAssociatorIso A D E F G hD hE P Q R).hom).app X.obj
  simpa only [Category.id_comp] using h

end SerrePositivity.DifferentialGraded.Morita
end

end CoherencePerfectAssociator

/-! ## Criterion（旧 SerrePositivity/DifferentialGraded/Morita/Criterion.lean） -/

/-! # U16c：三条件のMorita同値と実際の一般右随伴の統合

## 概要
Perf判定と全導来拡張の同値の逆関手を、U16aの実際の一般右随伴と同定する。
実際のunit/counitの可逆性と、その随伴そのものを使う同値を公開する。

## 方針
他担当の三条件判定・全導来拡張をそのまま再利用し、Mathlibの右随伴の一意性で比較する。

## 規約と注意
三条件と両側compact生成は明示した入力。局所Hom K-flat性・kernel列の射影性は追加しない。
抽象的に同値な別関手ではなく、公開主導来作用と公開unit/counitを比較する。

## 使われ方
U16cの最終統合、U17bのMorita同値の適用、一般右随伴を使う計算。
-/

@[expose] public section Criterion

noncomputable section
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (K : Kernel A D E) (hK : CriterionPerfConditions A D E K)
  {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A D)
  (hG : CriterionDerivedCompactGeneration A D G)
  {J : Type z'} [Small.{u} J] (H : J → DerivedModuleCategory A E)
  (hH : CriterionDerivedCompactGeneration A E H)

/-- 他担当の完成した三条件判定と全導来拡張による、実際のkernel作用の同値。 -/
def kernelMoritaEquivalence : DerivedModuleCategory A D ≌ DerivedModuleCategory A E :=
  criterionDerivedKernelEquivalenceOfMoritaConditions A D E K hK G hG H hH

/-- 構成したMorita同値の順方向は主導来作用そのもの。 -/
lemma kernelMoritaEquivalence_functor :
    (kernelMoritaEquivalence A D E K hK G hG H hH).functor = kernelDerivedTensor A D E K := rfl

/-- 一般右随伴は、別担当の全導来Morita同値の逆関手に自然同型である。 -/
def kernelMoritaHomIsoInverse : kernelDerivedHom A D E K ≅
    (kernelMoritaEquivalence A D E K hK G hG H hH).inverse :=
  Adjunction.rightAdjointUniq (kernelDerivedAdjunction A D E K)
    (kernelMoritaEquivalence A D E K hK G hG H hH).toAdjunction

/-- 右随伴の比較は実際の単位を同値の単位へ運ぶ。 -/
lemma kernelMoritaHomIsoInverse_unit :
    kernelDerivedUnit A D E K ≫ Functor.whiskerLeft (kernelDerivedTensor A D E K)
      (kernelMoritaHomIsoInverse A D E K hK G hG H hH).hom =
    (kernelMoritaEquivalence A D E K hK G hG H hH).unitIso.hom :=
  Adjunction.unit_rightAdjointUniq_hom (kernelDerivedAdjunction A D E K)
    (kernelMoritaEquivalence A D E K hK G hG H hH).toAdjunction

/-- 右随伴の比較は同値の余単位を実際の余単位へ運ぶ。 -/
lemma kernelMoritaHomIsoInverse_counit :
    Functor.whiskerRight (kernelMoritaHomIsoInverse A D E K hK G hG H hH).hom
      (kernelDerivedTensor A D E K) ≫
      (kernelMoritaEquivalence A D E K hK G hG H hH).counitIso.hom =
    kernelDerivedCounit A D E K :=
  Adjunction.rightAdjointUniq_hom_counit (kernelDerivedAdjunction A D E K)
    (kernelMoritaEquivalence A D E K hK G hG H hH).toAdjunction

include hK G hG H hH in
/-- 三条件とcompact生成の下で、U16aの実際の単位は自然同型である。 -/
lemma kernelMoritaUnit_isIso : IsIso (kernelDerivedUnit A D E K) := by
  let : (kernelDerivedTensor A D E K).IsEquivalence :=
    criterionDerivedKernelIsEquivalenceOfMoritaConditions A D E K hK G hG H hH
  change IsIso (kernelDerivedAdjunction A D E K).unit
  infer_instance

include hK G hG H hH in
/-- 三条件とcompact生成の下で、U16aの実際の余単位は自然同型である。 -/
lemma kernelMoritaCounit_isIso : IsIso (kernelDerivedCounit A D E K) := by
  let : (kernelDerivedTensor A D E K).IsEquivalence :=
    criterionDerivedKernelIsEquivalenceOfMoritaConditions A D E K hK G hG H hH
  change IsIso (kernelDerivedAdjunction A D E K).counit
  infer_instance

/-- 実際の一般右随伴と実際のunit/counitを持つMorita同値。 -/
def kernelMoritaAdjunctionEquivalence : DerivedModuleCategory A D ≌ DerivedModuleCategory A E := by
  let : IsIso (kernelDerivedAdjunction A D E K).unit :=
    kernelMoritaUnit_isIso A D E K hK G hG H hH
  let : IsIso (kernelDerivedAdjunction A D E K).counit :=
    kernelMoritaCounit_isIso A D E K hK G hG H hH
  let : ∀ X, IsIso ((kernelDerivedAdjunction A D E K).unit.app X) := fun _ => inferInstance
  let : ∀ Y, IsIso ((kernelDerivedAdjunction A D E K).counit.app Y) := fun _ => inferInstance
  exact (kernelDerivedAdjunction A D E K).toEquivalence

/-- 統合同値の順方向は元の主導来作用である。 -/
lemma kernelMoritaAdjunctionEquivalence_functor :
    (kernelMoritaAdjunctionEquivalence A D E K hK G hG H hH).functor =
      kernelDerivedTensor A D E K := rfl

/-- 統合同値の逆方向は構成済みの一般右随伴そのものである。 -/
lemma kernelMoritaAdjunctionEquivalence_inverse :
    (kernelMoritaAdjunctionEquivalence A D E K hK G hG H hH).inverse =
      kernelDerivedHom A D E K := rfl

/-- 統合同値の単位はU16aの実際の単位である。 -/
lemma kernelMoritaAdjunctionEquivalence_unit :
    (kernelMoritaAdjunctionEquivalence A D E K hK G hG H hH).unitIso.hom =
      kernelDerivedUnit A D E K := rfl

/-- 統合同値の余単位はU16aの実際の余単位である。 -/
lemma kernelMoritaAdjunctionEquivalence_counit :
    (kernelMoritaAdjunctionEquivalence A D E K hK G hG H hH).counitIso.hom =
      kernelDerivedCounit A D E K := rfl

end SerrePositivity.DifferentialGraded.Morita
end

end Criterion

/-! ## AdjunctionPerfectInverse（旧 SerrePositivity/DifferentialGraded/Morita/AdjunctionPerfectInverse.lean） -/

/-! # Perf Morita逆関手と一般右随伴の比較

## 概要
他担当のPerf同値の逆関手を、主導来圏への包含後に一般右随伴と比較する。

## 方針
Perf同値の作用比較と余単位から順方向の同型を作り、実際の導来随伴で転置する。

## 規約と注意
三条件と両側compact生成を明示する。列そのものの射影性や局所Hom条件は不要。

## 使われ方
U16cのPerf・全導来圏双方の逆関手を同じ右随伴へ統合する。
-/

@[expose] public section AdjunctionPerfectInverse

noncomputable section
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (K : Kernel A D E) (hK : CriterionPerfConditions A D E K)
  {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A D)
  (hG : CriterionDerivedCompactGeneration A D G)
  {J : Type z'} [Small.{u} J] (H : J → DerivedModuleCategory A E)
  (hH : CriterionDerivedCompactGeneration A E H)

/-- Perf判定の逆関手に実際の主作用を続けると終域Perfの包含になる。 -/
def kernelMoritaPerfInverseActionIso :
    ((criterionPerfEquivalenceOfConditions A D E K hK).equivalence.inverse ⋙
      perfectModuleInclusion A D Set.univ) ⋙ kernelDerivedTensor A D E K ≅
      perfectModuleInclusion A E Set.univ :=
  let W := criterionPerfEquivalenceOfConditions A D E K hK
  associator W.equivalence.inverse (perfectModuleInclusion A D Set.univ)
      (kernelDerivedTensor A D E K) ≪≫
    isoWhiskerLeft W.equivalence.inverse W.comparison ≪≫
    (associator W.equivalence.inverse W.equivalence.functor
      (perfectModuleInclusion A E Set.univ)).symm ≪≫
    isoWhiskerRight W.equivalence.counitIso (perfectModuleInclusion A E Set.univ) ≪≫
    leftUnitor (perfectModuleInclusion A E Set.univ)

/-- Perf判定の逆関手は、包含後に実際の一般右随伴へ自然同型である。 -/
def kernelMoritaPerfInverseIso :
    (criterionPerfEquivalenceOfConditions A D E K hK).equivalence.inverse ⋙
      perfectModuleInclusion A D Set.univ ≅
    perfectModuleInclusion A E Set.univ ⋙ kernelDerivedHom A D E K :=
  let S := (criterionPerfEquivalenceOfConditions A D E K hK).equivalence.inverse ⋙
    perfectModuleInclusion A D Set.univ
  let e := kernelMoritaAdjunctionEquivalence A D E K hK G hG H hH
  (rightUnitor S).symm ≪≫ isoWhiskerLeft S e.unitIso ≪≫
    (associator S (kernelDerivedTensor A D E K) (kernelDerivedHom A D E K)).symm ≪≫
    isoWhiskerRight (kernelMoritaPerfInverseActionIso A D E K hK) (kernelDerivedHom A D E K)

/-- Perf逆関手の比較は、実際の随伴の余単位で元の作用比較を計算する。 -/
lemma kernelMoritaPerfInverseIso_counit (X : PerfectModuleCategory A E) :
    (kernelDerivedTensor A D E K).map
        ((kernelMoritaPerfInverseIso A D E K hK G hG H hH).hom.app X) ≫
      (kernelDerivedCounit A D E K).app ((perfectModuleInclusion A E Set.univ).obj X) =
    (kernelMoritaPerfInverseActionIso A D E K hK).hom.app X := by
  let S := (criterionPerfEquivalenceOfConditions A D E K hK).equivalence.inverse ⋙
    perfectModuleInclusion A D Set.univ
  let a := (kernelMoritaPerfInverseActionIso A D E K hK).hom.app X
  have hn := (kernelDerivedCounit A D E K).naturality a
  simp only [Functor.comp_map, Functor.id_map] at hn
  have hc : (kernelMoritaPerfInverseIso A D E K hK G hG H hH).hom.app X =
      (kernelDerivedUnit A D E K).app (S.obj X) ≫ (kernelDerivedHom A D E K).map a := by
    change (𝟙 _ ≫ (kernelDerivedUnit A D E K).app (S.obj X) ≫
      𝟙 _ ≫ (kernelDerivedHom A D E K).map a) = _
    simp only [Category.id_comp]
  rw [hc, Functor.map_comp, Category.assoc, hn, ← Category.assoc]
  erw [kernelDerived_left_triangle A D E K (S.obj X), Category.id_comp]

end SerrePositivity.DifferentialGraded.Morita
end

end AdjunctionPerfectInverse
