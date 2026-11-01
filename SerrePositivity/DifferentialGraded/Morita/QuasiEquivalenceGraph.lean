module

public import SerrePositivity.DifferentialGraded.Derived.FunctorDerivedEquivalence
public import SerrePositivity.DifferentialGraded.Perfect.Compact.FiniteGeneration
public import SerrePositivity.DifferentialGraded.Morita.Kernel
public import SerrePositivity.DifferentialGraded.Morita.Perfect
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionNaturality
public import SerrePositivity.DifferentialGraded.Derived.BimoduleRestrictionEquivalence
public import SerrePositivity.DifferentialGraded.Endomorphism.Perfect
public import SerrePositivity.DifferentialGraded.Endomorphism.Enhancement

/-!
# Morita.QuasiEquivalenceGraph

## 概要
10 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## QuasiEquivalenceTriangles（旧 SerrePositivity/DifferentialGraded/Morita/QuasiEquivalenceTriangles.lean） -/

/-! # U16b：既存の導来擬同値と実際の随伴shift・三角構造

同値本体は既存dgFunctorDerivedEquivalenceを使い、順逆のshiftも既存の導来随伴のものを保つ。
-/

@[expose] public section QuasiEquivalenceTriangles
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

local instance moritaQuasiEquivalenceTrianglesLocal1 :
    (dgDerivedRestriction A D E F).CommShift ℤ := dgDerivedRestrictionCommShift A D E F
local instance moritaQuasiEquivalenceTrianglesLocal2 :
    (dgDerivedExtension A D E F).CommShift ℤ := dgDerivedExtensionCommShift A D E F

@[instance_reducible]
def quasiEquivalenceDerivedFunctorCommShift (hF : QuasiEquivalence F) :
    (dgFunctorDerivedEquivalence A D E F hF).functor.CommShift ℤ :=
  dgDerivedExtensionCommShift A D E F

@[instance_reducible]
def quasiEquivalenceDerivedInverseCommShift (hF : QuasiEquivalence F) :
    (dgFunctorDerivedEquivalence A D E F hF).inverse.CommShift ℤ :=
  dgDerivedRestrictionCommShift A D E F

attribute [local instance] quasiEquivalenceDerivedFunctorCommShift
  quasiEquivalenceDerivedInverseCommShift

lemma quasiEquivalenceDerivedCommShift (hF : QuasiEquivalence F) :
    (dgFunctorDerivedEquivalence A D E F hF).CommShift ℤ :=
  Equivalence.CommShift.mk' (dgFunctorDerivedEquivalence A D E F hF) ℤ
    (dgDerivedExtensionUnit_commShift A D E F)

lemma quasiEquivalenceDerivedIsTriangulated (hF : QuasiEquivalence F) :
    letI := quasiEquivalenceDerivedCommShift A D E F hF
    (dgFunctorDerivedEquivalence A D E F hF).IsTriangulated := by
  let := quasiEquivalenceDerivedCommShift A D E F hF
  exact Equivalence.IsTriangulated.mk' (dgFunctorDerivedEquivalence A D E F hF)
    (dgDerivedExtensionIsTriangulated A D E F)

/-- 同値の単位は既存の導来延長–制限の単位であり、そのshift整合性を保持する。 -/
lemma quasiEquivalenceDerivedUnitCommShift (hF : QuasiEquivalence F) :
    NatTrans.CommShift (dgFunctorDerivedEquivalence A D E F hF).unitIso.hom ℤ :=
  dgDerivedExtensionUnit_commShift A D E F

lemma quasiEquivalenceDerivedCounitCommShift (hF : QuasiEquivalence F) :
    NatTrans.CommShift (dgFunctorDerivedEquivalence A D E F hF).counitIso.hom ℤ :=
  dgDerivedExtensionCounit_commShift A D E F

end SerrePositivity.DifferentialGraded
end

end QuasiEquivalenceTriangles

/-! ## PerfectQuasiEquivalence（旧 SerrePositivity/DifferentialGraded/Morita/PerfectQuasiEquivalence.lean） -/

/-! # U16b：擬同値の実際の延長・制限を主Perfへ制限する

U13のPerfの最小性と既存の代表加群計算を使う。導来同値本体は変更しない。
-/

@[expose] public section PerfectQuasiEquivalence
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)
local instance moritaPerfectQuasiEquivalenceLocal1 :
    (dgDerivedRestriction A D E F).CommShift ℤ := dgDerivedRestrictionCommShift A D E F
local instance moritaPerfectQuasiEquivalenceLocal2 :
    (dgDerivedRestriction A D E F).IsTriangulated :=
  dgDerivedRestrictionIsTriangulated A D E F

lemma quasiEquivalenceRestriction_perfect (hF : QuasiEquivalence F)
    {X : DerivedModuleCategory A E} (hX : modulePerfect A E X) :
    modulePerfect A D ((dgDerivedRestriction A D E F).obj X) := by
  let P := (modulePerfect A D).inverseImage (dgDerivedRestriction A D E F)
  have : P.IsTriangulated := by dsimp [P]; infer_instance
  have : P.IsClosedUnderIsomorphisms := by dsimp [P]; infer_instance
  have : P.IsStableUnderRetracts :=
    ⟨fun r hY => (modulePerfect A D).prop_of_retract (r.map (dgDerivedRestriction A D E F)) hY⟩
  apply ((modulePerfect_le_iff_generators A E P).2 ?_) X hX
  intro e
  obtain ⟨d, ⟨ed⟩⟩ := dgDerivedExtension_representable_essImage A D E F hF.2 e
  exact (modulePerfect A D).prop_of_iso
    ((dgFunctorDerivedEquivalence A D E F hF).unitIso.app _ ≪≫
      (dgDerivedRestriction A D E F).mapIso ed)
    (modulePerfectOver_representable A D d (Set.mem_univ _))

lemma quasiEquivalenceExtension_perfect_iff (hF : QuasiEquivalence F)
    (X : DerivedModuleCategory A D) :
    modulePerfect A E ((dgDerivedExtension A D E F).obj X) ↔ modulePerfect A D X := by
  constructor
  · intro h
    exact (modulePerfect A D).prop_of_iso
      ((dgFunctorDerivedEquivalence A D E F hF).unitIso.app X).symm
      (quasiEquivalenceRestriction_perfect A D E F hF h)
  · exact dgDerivedExtension_perfect A D E F

lemma quasiEquivalenceRestriction_perfect_iff (hF : QuasiEquivalence F)
    (X : DerivedModuleCategory A E) :
    modulePerfect A D ((dgDerivedRestriction A D E F).obj X) ↔ modulePerfect A E X := by
  constructor
  · intro h
    exact (modulePerfect A E).prop_of_iso
      ((dgFunctorDerivedEquivalence A D E F hF).counitIso.app X)
      (dgDerivedExtension_perfect A D E F h)
  · exact quasiEquivalenceRestriction_perfect A D E F hF

/-- 任意dg関手の既存延長の、実際の主Perfへの制限。 -/
def quasiEquivalencePerfectExtension : PerfectModuleCategory A D ⥤ PerfectModuleCategory A E :=
  (modulePerfect A E).lift (perfectModuleInclusion A D Set.univ ⋙ dgDerivedExtension A D E F)
    (fun X => dgDerivedExtension_perfect A D E F X.property)

def quasiEquivalencePerfectRestriction (hF : QuasiEquivalence F) :
    PerfectModuleCategory A E ⥤ PerfectModuleCategory A D :=
  (modulePerfect A D).lift (perfectModuleInclusion A E Set.univ ⋙ dgDerivedRestriction A D E F)
    (fun X => quasiEquivalenceRestriction_perfect A D E F hF X.property)

def quasiEquivalencePerfectExtensionInclusionIso :
    quasiEquivalencePerfectExtension A D E F ⋙ perfectModuleInclusion A E Set.univ ≅
      perfectModuleInclusion A D Set.univ ⋙ dgDerivedExtension A D E F := Iso.refl _

def quasiEquivalencePerfectRestrictionInclusionIso (hF : QuasiEquivalence F) :
    quasiEquivalencePerfectRestriction A D E F hF ⋙ perfectModuleInclusion A D Set.univ ≅
      perfectModuleInclusion A E Set.univ ⋙ dgDerivedRestriction A D E F := Iso.refl _

/-- 順逆とも元の実際の関手の制限。単位・余単位も元の導来同値の成分を保つ。 -/
def quasiEquivalencePerfectEquivalence (hF : QuasiEquivalence F) :
    PerfectModuleCategory A D ≌ PerfectModuleCategory A E where
  functor := quasiEquivalencePerfectExtension A D E F
  inverse := quasiEquivalencePerfectRestriction A D E F hF
  unitIso := NatIso.ofComponents
    (fun X => (modulePerfect A D).isoMk
      ((dgFunctorDerivedEquivalence A D E F hF).unitIso.app X.obj))
    (by intro X Y f; apply (modulePerfect A D).hom_ext
        exact (dgFunctorDerivedEquivalence A D E F hF).unitIso.hom.naturality f.hom)
  counitIso := NatIso.ofComponents
    (fun X => (modulePerfect A E).isoMk
      ((dgFunctorDerivedEquivalence A D E F hF).counitIso.app X.obj))
    (by intro X Y f; apply (modulePerfect A E).hom_ext
        exact (dgFunctorDerivedEquivalence A D E F hF).counitIso.hom.naturality f.hom)
  functor_unitIso_comp X := by
    apply (modulePerfect A E).hom_ext
    exact (dgFunctorDerivedEquivalence A D E F hF).functor_unitIso_comp X.obj

lemma quasiEquivalencePerfectUnit_inclusion (hF : QuasiEquivalence F)
    (X : PerfectModuleCategory A D) :
    (perfectModuleInclusion A D Set.univ).map
        ((quasiEquivalencePerfectEquivalence A D E F hF).unitIso.hom.app X) =
      (dgDerivedExtensionUnit A D E F).app X.obj := rfl

lemma quasiEquivalencePerfectCounit_inclusion (hF : QuasiEquivalence F)
    (X : PerfectModuleCategory A E) :
    (perfectModuleInclusion A E Set.univ).map
        ((quasiEquivalencePerfectEquivalence A D E F hF).counitIso.hom.app X) =
      (dgDerivedExtensionCounit A D E F).app X.obj := rfl

end SerrePositivity.DifferentialGraded
end

end PerfectQuasiEquivalence

/-! ## PerfectQuasiEquivalenceTriangles（旧 SerrePositivity/DifferentialGraded/Morita/PerfectQuasiEquivalenceTriangles.lean） -/

/-! # 実際の主Perf制限の随伴shift・三角構造と包含の図式 -/

@[expose] public section PerfectQuasiEquivalenceTriangles
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)
local instance moritaPerfectQuasiEquivalenceTrianglesLocal1 :
    (perfectModuleInclusion A D Set.univ).Full :=
  inferInstanceAs ((modulePerfect A D).ι.Full)
local instance moritaPerfectQuasiEquivalenceTrianglesLocal2 :
    (perfectModuleInclusion A D Set.univ).Faithful :=
  inferInstanceAs ((modulePerfect A D).ι.Faithful)
local instance moritaPerfectQuasiEquivalenceTrianglesLocal3 :
    (perfectModuleInclusion A E Set.univ).Full :=
  inferInstanceAs ((modulePerfect A E).ι.Full)
local instance moritaPerfectQuasiEquivalenceTrianglesLocal4 :
    (perfectModuleInclusion A E Set.univ).Faithful :=
  inferInstanceAs ((modulePerfect A E).ι.Faithful)
local instance moritaPerfectQuasiEquivalenceTrianglesLocal5 :
    (dgDerivedRestriction A D E F).CommShift ℤ := dgDerivedRestrictionCommShift A D E F
local instance moritaPerfectQuasiEquivalenceTrianglesLocal6 :
    (dgDerivedExtension A D E F).CommShift ℤ := dgDerivedExtensionCommShift A D E F
local instance moritaPerfectQuasiEquivalenceTrianglesLocal7 :
    (dgDerivedRestriction A D E F).IsTriangulated :=
  dgDerivedRestrictionIsTriangulated A D E F
local instance moritaPerfectQuasiEquivalenceTrianglesLocal8 :
    (dgDerivedExtension A D E F).IsTriangulated :=
  dgDerivedExtensionIsTriangulated A D E F

@[instance_reducible]
def quasiEquivalencePerfectExtensionCommShift :
    (quasiEquivalencePerfectExtension A D E F).CommShift ℤ :=
  Functor.CommShift.ofComp (quasiEquivalencePerfectExtensionInclusionIso A D E F) ℤ

@[instance_reducible]
def quasiEquivalencePerfectRestrictionCommShift (hF : QuasiEquivalence F) :
    (quasiEquivalencePerfectRestriction A D E F hF).CommShift ℤ :=
  Functor.CommShift.ofComp (quasiEquivalencePerfectRestrictionInclusionIso A D E F hF) ℤ

attribute [local instance] quasiEquivalencePerfectExtensionCommShift
  quasiEquivalencePerfectRestrictionCommShift

lemma quasiEquivalencePerfectExtensionInclusionCommShift :
    NatTrans.CommShift (quasiEquivalencePerfectExtensionInclusionIso A D E F).hom ℤ :=
  Functor.CommShift.ofComp_compatibility (quasiEquivalencePerfectExtensionInclusionIso A D E F) ℤ

lemma quasiEquivalencePerfectRestrictionInclusionCommShift (hF : QuasiEquivalence F) :
    NatTrans.CommShift (quasiEquivalencePerfectRestrictionInclusionIso A D E F hF).hom ℤ :=
  Functor.CommShift.ofComp_compatibility
    (quasiEquivalencePerfectRestrictionInclusionIso A D E F hF) ℤ

attribute [local instance] quasiEquivalencePerfectExtensionInclusionCommShift
  quasiEquivalencePerfectRestrictionInclusionCommShift

lemma quasiEquivalencePerfectExtensionIsTriangulated :
    (quasiEquivalencePerfectExtension A D E F).IsTriangulated :=
  (Functor.isTriangulated_iff_comp_right
    (quasiEquivalencePerfectExtensionInclusionIso A D E F)).2 inferInstance

lemma quasiEquivalencePerfectRestrictionIsTriangulated (hF : QuasiEquivalence F) :
    (quasiEquivalencePerfectRestriction A D E F hF).IsTriangulated :=
  (Functor.isTriangulated_iff_comp_right
    (quasiEquivalencePerfectRestrictionInclusionIso A D E F hF)).2 inferInstance

local instance moritaPerfectQuasiEquivalenceTrianglesLocal9 (hF : QuasiEquivalence F) :
    (quasiEquivalencePerfectEquivalence A D E F hF).functor.CommShift ℤ :=
  quasiEquivalencePerfectExtensionCommShift A D E F
local instance moritaPerfectQuasiEquivalenceTrianglesLocal10 (hF : QuasiEquivalence F) :
    (quasiEquivalencePerfectEquivalence A D E F hF).inverse.CommShift ℤ :=
  quasiEquivalencePerfectRestrictionCommShift A D E F hF

lemma quasiEquivalencePerfectUnitCommShift (hF : QuasiEquivalence F) :
    NatTrans.CommShift (quasiEquivalencePerfectEquivalence A D E F hF).unitIso.hom ℤ := by
  let := dgDerivedExtensionUnit_commShift A D E F
  let I := perfectModuleInclusion A D Set.univ
  let J := perfectModuleInclusion A E Set.univ
  let L := dgDerivedExtension A D E F
  let R := dgDerivedRestriction A D E F
  let Lp := quasiEquivalencePerfectExtension A D E F
  let Rp := quasiEquivalencePerfectRestriction A D E F hF
  let α := quasiEquivalencePerfectExtensionInclusionIso A D E F
  let β := quasiEquivalencePerfectRestrictionInclusionIso A D E F hF
  have he : Functor.whiskerRight
      (quasiEquivalencePerfectEquivalence A D E F hF).unitIso.hom I =
      (Functor.leftUnitor I).hom ≫ (Functor.rightUnitor I).inv ≫
        Functor.whiskerLeft I (dgDerivedExtensionUnit A D E F) ≫
        (Functor.associator I L R).inv ≫ Functor.whiskerRight α.inv R ≫
        (Functor.associator Lp J R).hom ≫ Functor.whiskerLeft Lp β.inv ≫
        (Functor.associator Lp Rp I).inv := by
    apply NatTrans.ext
    funext X
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
      Functor.associator_inv_app, Functor.associator_hom_app]
    change (dgDerivedExtensionUnit A D E F).app X.obj =
      𝟙 _ ≫ 𝟙 _ ≫ (dgDerivedExtensionUnit A D E F).app X.obj ≫
        𝟙 _ ≫ R.map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    exact (Category.comp_id _).symm
  exact NatTrans.CommShift.of_comp_faithful (G := I) (h := by rw [he]; infer_instance)

lemma quasiEquivalencePerfectCommShift (hF : QuasiEquivalence F) :
    (quasiEquivalencePerfectEquivalence A D E F hF).CommShift ℤ :=
  Equivalence.CommShift.mk' _ _ (quasiEquivalencePerfectUnitCommShift A D E F hF)

lemma quasiEquivalencePerfectCounitCommShift (hF : QuasiEquivalence F) :
    NatTrans.CommShift (quasiEquivalencePerfectEquivalence A D E F hF).counitIso.hom ℤ := by
  let := quasiEquivalencePerfectCommShift A D E F hF
  infer_instance

lemma quasiEquivalencePerfectIsTriangulated (hF : QuasiEquivalence F) :
    letI := quasiEquivalencePerfectCommShift A D E F hF
    (quasiEquivalencePerfectEquivalence A D E F hF).IsTriangulated := by
  let := quasiEquivalencePerfectCommShift A D E F hF
  exact Equivalence.IsTriangulated.mk' _ (quasiEquivalencePerfectExtensionIsTriangulated A D E F)

def quasiEquivalencePerfectExtensionTriangleIso :
    (quasiEquivalencePerfectExtension A D E F).mapTriangle ⋙
        (perfectModuleInclusion A E Set.univ).mapTriangle ≅
      (perfectModuleInclusion A D Set.univ).mapTriangle ⋙
        (dgDerivedExtension A D E F).mapTriangle :=
  (Functor.mapTriangleCompIso _ _).symm ≪≫
    Functor.mapTriangleIso (quasiEquivalencePerfectExtensionInclusionIso A D E F) ≪≫
    Functor.mapTriangleCompIso _ _

def quasiEquivalencePerfectRestrictionTriangleIso (hF : QuasiEquivalence F) :
    (quasiEquivalencePerfectRestriction A D E F hF).mapTriangle ⋙
        (perfectModuleInclusion A D Set.univ).mapTriangle ≅
      (perfectModuleInclusion A E Set.univ).mapTriangle ⋙
        (dgDerivedRestriction A D E F).mapTriangle :=
  (Functor.mapTriangleCompIso _ _).symm ≪≫
    Functor.mapTriangleIso (quasiEquivalencePerfectRestrictionInclusionIso A D E F hF) ≪≫
    Functor.mapTriangleCompIso _ _

end SerrePositivity.DifferentialGraded
end

end PerfectQuasiEquivalenceTriangles

/-! ## PerfectEnhancementComparison（旧 SerrePositivity/DifferentialGraded/Morita/PerfectEnhancementComparison.lean） -/

/-! # U16bとU13の小さい主dg enhancementの比較

実際の導来延長のPerf制限をU13の既存同値で小さいH⁰へ運び、比較正方形を保つ。
このH⁰の運搬を新たなdg関手の構成と同一視しない。dgの証拠は入力FのQuasiEquivalenceである。
-/

@[expose] public section PerfectEnhancementComparison
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)
local instance moritaPerfectEnhancementComparisonLocal1 :
    (quasiEquivalencePerfectExtension A D E F).CommShift ℤ :=
  quasiEquivalencePerfectExtensionCommShift A D E F
local instance moritaPerfectEnhancementComparisonLocal2 (hF : QuasiEquivalence F) :
    (quasiEquivalencePerfectEquivalence A D E F hF).functor.CommShift ℤ :=
  quasiEquivalencePerfectExtensionCommShift A D E F
local instance moritaPerfectEnhancementComparisonLocal3 (hF : QuasiEquivalence F) :
    (quasiEquivalencePerfectEquivalence A D E F hF).inverse.CommShift ℤ :=
  quasiEquivalencePerfectRestrictionCommShift A D E F hF
local instance moritaPerfectEnhancementComparisonLocal4 (hF : QuasiEquivalence F) :
    (quasiEquivalencePerfectEquivalence A D E F hF).CommShift ℤ :=
  quasiEquivalencePerfectCommShift A D E F hF
local instance moritaPerfectEnhancementComparisonLocal5 (hF : QuasiEquivalence F) :
    (quasiEquivalencePerfectEquivalence A D E F hF).IsTriangulated :=
  quasiEquivalencePerfectIsTriangulated A D E F hF

def quasiEquivalenceSmallPerfectHomotopyEquivalence (hF : QuasiEquivalence F) :
    SmallPerfectDGHomotopyCategoryOver A D Set.univ ≌
      SmallPerfectDGHomotopyCategoryOver A E Set.univ :=
  ((smallPerfectDGModuleHomotopyEquivalence A D Set.univ).trans
    (quasiEquivalencePerfectEquivalence A D E F hF)).trans
      (smallPerfectDGModuleHomotopyEquivalence A E Set.univ).symm

instance quasiEquivalenceSmallPerfectHomotopyFunctorCommShift (hF : QuasiEquivalence F) :
    (quasiEquivalenceSmallPerfectHomotopyEquivalence A D E F hF).functor.CommShift ℤ :=
  by
    unfold quasiEquivalenceSmallPerfectHomotopyEquivalence
    infer_instance

instance quasiEquivalenceSmallPerfectHomotopyInverseCommShift (hF : QuasiEquivalence F) :
    (quasiEquivalenceSmallPerfectHomotopyEquivalence A D E F hF).inverse.CommShift ℤ :=
  by
    unfold quasiEquivalenceSmallPerfectHomotopyEquivalence
    infer_instance

instance quasiEquivalenceSmallPerfectHomotopyCommShift (hF : QuasiEquivalence F) :
    (quasiEquivalenceSmallPerfectHomotopyEquivalence A D E F hF).CommShift ℤ := by
  unfold quasiEquivalenceSmallPerfectHomotopyEquivalence
  infer_instance

instance quasiEquivalenceSmallPerfectHomotopyIsTriangulated (hF : QuasiEquivalence F) :
    (quasiEquivalenceSmallPerfectHomotopyEquivalence A D E F hF).IsTriangulated := by
  unfold quasiEquivalenceSmallPerfectHomotopyEquivalence
  infer_instance

def quasiEquivalenceSmallPerfectComparisonIso (hF : QuasiEquivalence F) :
    (quasiEquivalenceSmallPerfectHomotopyEquivalence A D E F hF).functor ⋙
        smallPerfectDGModuleToPerfect A E Set.univ ≅
      smallPerfectDGModuleToPerfect A D Set.univ ⋙ quasiEquivalencePerfectExtension A D E F :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (smallPerfectDGModuleHomotopyEquivalence A E Set.univ).counitIso ≪≫
      Functor.rightUnitor _

instance quasiEquivalenceSmallPerfectComparisonCommShift (hF : QuasiEquivalence F) :
    NatTrans.CommShift (quasiEquivalenceSmallPerfectComparisonIso A D E F hF).hom ℤ := by
  change NatTrans.CommShift
    ((Functor.associator
      ((smallPerfectDGModuleHomotopyEquivalence A D Set.univ).functor ⋙
        (quasiEquivalencePerfectEquivalence A D E F hF).functor)
      (smallPerfectDGModuleHomotopyEquivalence A E Set.univ).inverse
      (smallPerfectDGModuleHomotopyEquivalence A E Set.univ).functor).hom ≫
    Functor.whiskerLeft _ (smallPerfectDGModuleHomotopyEquivalence A E Set.univ).counitIso.hom ≫
    (Functor.rightUnitor _).hom) ℤ
  infer_instance

def quasiEquivalenceSmallPerfectComparisonTriangleIso (hF : QuasiEquivalence F) :
    (quasiEquivalenceSmallPerfectHomotopyEquivalence A D E F hF).functor.mapTriangle ⋙
        (smallPerfectDGModuleToPerfect A E Set.univ).mapTriangle ≅
      (smallPerfectDGModuleToPerfect A D Set.univ).mapTriangle ⋙
        (quasiEquivalencePerfectExtension A D E F).mapTriangle :=
  (Functor.mapTriangleCompIso _ _).symm ≪≫
    Functor.mapTriangleIso (quasiEquivalenceSmallPerfectComparisonIso A D E F hF) ≪≫
    Functor.mapTriangleCompIso _ _

end SerrePositivity.DifferentialGraded
end

end PerfectEnhancementComparison

/-! ## QuasiEquivalenceGraph（旧 SerrePositivity/DifferentialGraded/Morita/QuasiEquivalenceGraph.lean） -/

/-! # U16aの通常graph作用と既存導来延長の計算モデル

主導来kernel作用の実装前にも、任意射影解像度での通常graph計算を公開する。
主導来kernel作用との全射自然な同型はそのAPIの実装後に別途接続する。
-/

@[expose] public section QuasiEquivalenceGraph
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

def quasiEquivalenceGraphResolutionComputation {M : ModuleCategory A D}
    (R : ModuleProjectiveResolution A D M) :
    (dgDerivedExtension A D E F).obj ((moduleToDerived A D).obj M) ≅
      (moduleToDerived A E).obj
        ((kernelTensor A D E (functorGraph A D E F)).onClosed.obj R.obj) := by
  rw [kernelTensor_graph]
  exact dgDerivedExtensionResolutionComputation A D E F R

lemma quasiEquivalenceGraphResolution_perfect {M : ModuleCategory A D}
    (hM : modulePerfect A D ((moduleToDerived A D).obj M))
    (R : ModuleProjectiveResolution A D M) :
    modulePerfect A E ((moduleToDerived A E).obj
      ((kernelTensor A D E (functorGraph A D E F)).onClosed.obj R.obj)) :=
  (modulePerfect A E).prop_of_iso (quasiEquivalenceGraphResolutionComputation A D E F R)
    (dgDerivedExtension_perfect A D E F hM)

end SerrePositivity.DifferentialGraded.Morita
end

end QuasiEquivalenceGraph

/-! ## QuasiEquivalenceGraphNaturality（旧 SerrePositivity/DifferentialGraded/Morita/QuasiEquivalenceGraphNaturality.lean） -/

/-! # graph作用の自然な解像度モデルと主局所化による比較の復元

将来のU16a関手Kについて、通常graph作用による自然な計算同型を入力すると、
主導来関手の自然同型を復元する。対象ごとの同型だけを自然性の代用にしない。
-/

@[expose] public section QuasiEquivalenceGraphNaturality
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

def quasiEquivalenceGraphResolutionModel
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    ModuleCategory A D ⥤ DerivedModuleCategory A E :=
  moduleResolutionHomotopyFunctor A D R ⋙
    (kernelTensor A D E (functorGraph A D E F)).onHomotopy ⋙ moduleHomotopyToDerivedClosed A E

/-- 既存導来延長は、任意解像度族によるgraphモデルを自然に計算する。 -/
def quasiEquivalenceGraphDerivedModelIso
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleToDerived A D ⋙ dgDerivedExtension A D E F ≅
      quasiEquivalenceGraphResolutionModel A D E F R :=
  Functor.isoWhiskerLeft (moduleToDerived A D)
      (dgResolutionDerivedExtensionIso A D E F (moduleCanonicalProjectiveResolution A D) R) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleDerivedResolutionFunctor_fac A D R) _

/-- 通常graphの射影解像度計算は、元の加群の射と選んだliftに自然。 -/
lemma quasiEquivalenceGraphResolutionModel_naturality
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    {M N : ModuleCategory A D} (f : M ⟶ N) :
    (dgResolutionDerivedExtension A D E F R).map ((moduleToDerived A D).map f) ≫
        (dgResolutionDerivedExtensionComputation A D E F R N).hom =
      (dgResolutionDerivedExtensionComputation A D E F R M).hom ≫
        (moduleToDerived A E).map
          ((kernelTensor A D E (functorGraph A D E F)).onClosed.map ((R M).lift (R N) f)) :=
  dgResolutionDerivedExtensionComputation_naturality A D E F R f

/-- 自然なgraph計算同型を持つ指定関手Kを、既存導来延長へ比較する。 -/
def quasiEquivalenceGraphComparisonOfModel
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (K : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    (eK : moduleToDerived A D ⋙ K ≅ quasiEquivalenceGraphResolutionModel A D E F R) :
    K ≅ dgDerivedExtension A D E F :=
  (Localization.fullyFaithfulWhiskeringLeft (moduleToDerived A D) (moduleQuasiIso A D)
    (DerivedModuleCategory A E)).preimageIso
      (eK ≪≫ (quasiEquivalenceGraphDerivedModelIso A D E F R).symm)

lemma quasiEquivalenceGraphComparisonOfModel_precomp
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (K : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    (eK : moduleToDerived A D ⋙ K ≅ quasiEquivalenceGraphResolutionModel A D E F R) :
    Functor.whiskerLeft (moduleToDerived A D)
        (quasiEquivalenceGraphComparisonOfModel A D E F R K eK).hom =
      (eK ≪≫ (quasiEquivalenceGraphDerivedModelIso A D E F R).symm).hom :=
  (Localization.fullyFaithfulWhiskeringLeft (moduleToDerived A D) (moduleQuasiIso A D)
    (DerivedModuleCategory A E)).map_preimage _

lemma quasiEquivalenceGraphComparisonOfModel_unique
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (K : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    (eK : moduleToDerived A D ⋙ K ≅ quasiEquivalenceGraphResolutionModel A D E F R)
    (α : K ⟶ dgDerivedExtension A D E F)
    (hα : Functor.whiskerLeft (moduleToDerived A D) α =
      (eK ≪≫ (quasiEquivalenceGraphDerivedModelIso A D E F R).symm).hom) :
    α = (quasiEquivalenceGraphComparisonOfModel A D E F R K eK).hom := by
  apply (Localization.fullyFaithfulWhiskeringLeft (moduleToDerived A D)
    (moduleQuasiIso A D) (DerivedModuleCategory A E)).map_injective
  exact hα.trans (quasiEquivalenceGraphComparisonOfModel_precomp A D E F R K eK).symm

lemma quasiEquivalenceGraphComparisonOfModel_perfect
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (K : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    (eK : moduleToDerived A D ⋙ K ≅ quasiEquivalenceGraphResolutionModel A D E F R)
    {X : DerivedModuleCategory A D} (hX : modulePerfect A D X) :
    modulePerfect A E (K.obj X) :=
  (modulePerfect A E).prop_of_iso
    ((quasiEquivalenceGraphComparisonOfModel A D E F R K eK).app X).symm
    (dgDerivedExtension_perfect A D E F hX)

lemma quasiEquivalenceGraphComparisonOfModel_isEquivalence
    (hF : QuasiEquivalence F)
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (K : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    (eK : moduleToDerived A D ⋙ K ≅ quasiEquivalenceGraphResolutionModel A D E F R) :
    K.IsEquivalence := by
  let : (dgDerivedExtension A D E F).IsEquivalence :=
    (dgFunctorDerivedEquivalence A D E F hF).isEquivalence_functor
  exact Functor.isEquivalence_of_iso
    (quasiEquivalenceGraphComparisonOfModel A D E F R K eK).symm

def quasiEquivalenceGraphComparisonOnPerfect
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (K : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    (eK : moduleToDerived A D ⋙ K ≅ quasiEquivalenceGraphResolutionModel A D E F R) :
    perfectFunctorRestriction A D E K
        (fun _ h => quasiEquivalenceGraphComparisonOfModel_perfect A D E F R K eK h) ≅
      perfectFunctorRestriction A D E (dgDerivedExtension A D E F)
        (fun _ h => dgDerivedExtension_perfect A D E F h) :=
  perfectFunctorIso A D E K (dgDerivedExtension A D E F)
    (fun _ h => quasiEquivalenceGraphComparisonOfModel_perfect A D E F R K eK h)
    (fun _ h => dgDerivedExtension_perfect A D E F h)
    (quasiEquivalenceGraphComparisonOfModel A D E F R K eK)

end SerrePositivity.DifferentialGraded.Morita
end

end QuasiEquivalenceGraphNaturality

/-! ## QuasiEquivalenceGraphAction（旧 SerrePositivity/DifferentialGraded/Morita/QuasiEquivalenceGraphAction.lean） -/

/-! # U16aの実際の通常kernel導来作用とU16bのgraph比較

公開済みkernelDerivedTensorOnBimoduleを使う。kernel変数の局所化への降下は別のU16a API。
同値本体・随伴・単位・余単位は既存の導来延長–制限のものを保つ。
-/

@[expose] public section QuasiEquivalenceGraphAction
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- 公開済みの実際の通常kernel導来作用から、既存導来延長への関手自然同型。 -/
def quasiEquivalenceGraphActionIso :
    kernelDerivedTensorOnBimodule A D E (functorGraph A D E F) ≅ dgDerivedExtension A D E F :=
  eqToIso (kernelDerivedTensorOnBimodule_graph A D E F)

lemma quasiEquivalenceGraphDerivedEquivalence_functor (hF : QuasiEquivalence F) :
    (dgFunctorDerivedEquivalence A D E F hF).functor =
      kernelDerivedTensorOnBimodule A D E (functorGraph A D E F) := rfl

@[instance_reducible]
def quasiEquivalenceGraphActionCommShift :
    (kernelDerivedTensorOnBimodule A D E (functorGraph A D E F)).CommShift ℤ :=
  dgDerivedExtensionCommShift A D E F

attribute [local instance] quasiEquivalenceGraphActionCommShift
local instance moritaGraphActionExtensionShift : (dgDerivedExtension A D E F).CommShift ℤ :=
  dgDerivedExtensionCommShift A D E F

lemma quasiEquivalenceGraphActionIsoCommShift :
    NatTrans.CommShift (quasiEquivalenceGraphActionIso A D E F).hom ℤ := by
  change NatTrans.CommShift (𝟙 (dgDerivedExtension A D E F)) ℤ
  infer_instance

lemma quasiEquivalenceGraphActionIsTriangulated :
    (kernelDerivedTensorOnBimodule A D E (functorGraph A D E F)).IsTriangulated :=
  dgDerivedExtensionIsTriangulated A D E F

lemma quasiEquivalenceGraphAction_perfect {X : DerivedModuleCategory A D}
    (hX : modulePerfect A D X) :
    modulePerfect A E
      ((kernelDerivedTensorOnBimodule A D E (functorGraph A D E F)).obj X) :=
  dgDerivedExtension_perfect A D E F hX

def quasiEquivalenceGraphActionOnPerfectIso :
    perfectFunctorRestriction A D E
        (kernelDerivedTensorOnBimodule A D E (functorGraph A D E F))
        (fun _ h => quasiEquivalenceGraphAction_perfect A D E F h) ≅
      quasiEquivalencePerfectExtension A D E F :=
  perfectFunctorIso A D E _ _
    (fun _ h => quasiEquivalenceGraphAction_perfect A D E F h)
    (fun _ h => dgDerivedExtension_perfect A D E F h)
    (quasiEquivalenceGraphActionIso A D E F)

/-- 自然モデルから復元した比較も、公開された実際のgraph比較と一致する。 -/
lemma quasiEquivalenceGraphActionComparisonOfModel
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    quasiEquivalenceGraphComparisonOfModel A D E F R
        (kernelDerivedTensorOnBimodule A D E (functorGraph A D E F))
        (Functor.isoWhiskerLeft (moduleToDerived A D) (quasiEquivalenceGraphActionIso A D E F) ≪≫
          quasiEquivalenceGraphDerivedModelIso A D E F R) =
      quasiEquivalenceGraphActionIso A D E F := by
  apply Iso.ext
  symm
  apply quasiEquivalenceGraphComparisonOfModel_unique
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

end SerrePositivity.DifferentialGraded.Morita
end

end QuasiEquivalenceGraphAction

/-! ## QuasiEquivalenceProducts（旧 SerrePositivity/DifferentialGraded/Morita/QuasiEquivalenceProducts.lean） -/

/-! # U16b：積dg圏の擬同値と局所Hom条件を保持したPerf制限

既存の導来bimodule制限の条件hC・hDを保ち、積のHomのtensorが無条件に擬同型とはしない。
-/

@[expose] public section QuasiEquivalenceProducts
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (F : DGFunctor A B D) (G : DGFunctor A C E)
  (hF : QuasiEquivalence F) (hG : QuasiEquivalence G)
  (hC : localHomKFlat A C) (hD : localHomKFlat A D)

def quasiEquivalenceProductPerfectRestrictionEquivalence :
    PerfectModuleCategory A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ ≌
      PerfectModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ :=
  (quasiEquivalencePerfectEquivalence A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
    (DGTensorCategory A Dᵒᵖ E)ᵒᵖ (F.op.tensor G).op
    (bimoduleRestrictionDG_quasiEquivalence A B C D E F G hF hG hC hD)).symm

def quasiEquivalenceProductPerfectRestrictionSquare :
    (quasiEquivalenceProductPerfectRestrictionEquivalence A B C D E F G hF hG hC hD).functor ⋙
        perfectModuleInclusion A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ Set.univ ≅
      perfectModuleInclusion A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ Set.univ ⋙
        bimoduleRestrictionModuleDerived A B C D E F G :=
  quasiEquivalencePerfectRestrictionInclusionIso A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
    (DGTensorCategory A Dᵒᵖ E)ᵒᵖ (F.op.tensor G).op
    (bimoduleRestrictionDG_quasiEquivalence A B C D E F G hF hG hC hD)

end SerrePositivity.DifferentialGraded
end

end QuasiEquivalenceProducts

/-! ## QuasiEquivalenceDerivedGraph（旧 SerrePositivity/DifferentialGraded/Morita/QuasiEquivalenceDerivedGraph.lean） -/

/-! # 主導来kernel上の実際のgraph作用と既存導来擬同値の比較

U16aの公開済み降下APIを使い、通常kernel版の比較を主導来graphへ移す。
随伴・単位・余単位は既存の延長–制限随伴から自然同型に沿って運ぶ。
-/

@[expose] public section QuasiEquivalenceDerivedGraph
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

def quasiEquivalenceDerivedGraphIso :
    kernelDerivedTensor A D E (kernelGraph A D E F) ≅ dgDerivedExtension A D E F :=
  kernelDerivedTensorOnBimoduleIso A D E (BimoduleCategory.of A E D (functorGraph A D E F)) ≪≫
    quasiEquivalenceGraphActionIso A D E F

local instance moritaDerivedGraphExtensionShift : (dgDerivedExtension A D E F).CommShift ℤ :=
  dgDerivedExtensionCommShift A D E F

@[instance_reducible]
def quasiEquivalenceDerivedGraphCommShift :
    (kernelDerivedTensor A D E (kernelGraph A D E F)).CommShift ℤ :=
  Functor.CommShift.ofIso (quasiEquivalenceDerivedGraphIso A D E F).symm ℤ

attribute [local instance] quasiEquivalenceDerivedGraphCommShift

lemma quasiEquivalenceDerivedGraphIsoCommShift :
    NatTrans.CommShift (quasiEquivalenceDerivedGraphIso A D E F).hom ℤ := by
  let : NatTrans.CommShift (quasiEquivalenceDerivedGraphIso A D E F).symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility (quasiEquivalenceDerivedGraphIso A D E F).symm ℤ
  exact NatTrans.CommShift.of_iso_inv (quasiEquivalenceDerivedGraphIso A D E F).symm ℤ

attribute [local instance] quasiEquivalenceDerivedGraphIsoCommShift

lemma quasiEquivalenceDerivedGraphIsTriangulated :
    (kernelDerivedTensor A D E (kernelGraph A D E F)).IsTriangulated := by
  let := dgDerivedExtensionIsTriangulated A D E F
  exact Functor.isTriangulated_of_iso (quasiEquivalenceDerivedGraphIso A D E F).symm

lemma quasiEquivalenceDerivedGraphIsEquivalence (hF : QuasiEquivalence F) :
    (kernelDerivedTensor A D E (kernelGraph A D E F)).IsEquivalence := by
  let : (dgDerivedExtension A D E F).IsEquivalence :=
    (dgFunctorDerivedEquivalence A D E F hF).isEquivalence_functor
  exact Functor.isEquivalence_of_iso (quasiEquivalenceDerivedGraphIso A D E F).symm

def quasiEquivalenceDerivedGraphAdjunction :
    kernelDerivedTensor A D E (kernelGraph A D E F) ⊣ dgDerivedRestriction A D E F :=
  (dgDerivedExtensionRestrictionAdjunction A D E F).ofNatIsoLeft
    (quasiEquivalenceDerivedGraphIso A D E F).symm

lemma quasiEquivalenceDerivedGraphUnit_app (X : DerivedModuleCategory A D) :
    (quasiEquivalenceDerivedGraphAdjunction A D E F).unit.app X =
      (dgDerivedExtensionUnit A D E F).app X ≫
        (dgDerivedRestriction A D E F).map
          ((quasiEquivalenceDerivedGraphIso A D E F).inv.app X) := rfl

lemma quasiEquivalenceDerivedGraphCounit_app (Y : DerivedModuleCategory A E) :
    (quasiEquivalenceDerivedGraphAdjunction A D E F).counit.app Y =
      (quasiEquivalenceDerivedGraphIso A D E F).hom.app ((dgDerivedRestriction A D E F).obj Y) ≫
        (dgDerivedExtensionCounit A D E F).app Y := rfl

lemma quasiEquivalenceDerivedGraph_perfect {X : DerivedModuleCategory A D}
    (hX : modulePerfect A D X) :
    modulePerfect A E ((kernelDerivedTensor A D E (kernelGraph A D E F)).obj X) :=
  (modulePerfect A E).prop_of_iso ((quasiEquivalenceDerivedGraphIso A D E F).app X).symm
    (dgDerivedExtension_perfect A D E F hX)

def quasiEquivalenceDerivedGraphOnPerfectIso :
    perfectFunctorRestriction A D E (kernelDerivedTensor A D E (kernelGraph A D E F))
        (fun _ h => quasiEquivalenceDerivedGraph_perfect A D E F h) ≅
      quasiEquivalencePerfectExtension A D E F :=
  perfectFunctorIso A D E _ _
    (fun _ h => quasiEquivalenceDerivedGraph_perfect A D E F h)
    (fun _ h => dgDerivedExtension_perfect A D E F h) (quasiEquivalenceDerivedGraphIso A D E F)

end SerrePositivity.DifferentialGraded.Morita
end

end QuasiEquivalenceDerivedGraph

/-! ## QuasiEquivalenceEndomorphismComparison（旧 SerrePositivity/DifferentialGraded/Morita/QuasiEquivalenceEndomorphismComparison.lean） -/

/-! # U16bとU14の実際のtensor–Hom比較の接続

擬同値に沿う延長の後に、指定したU14生成元のHomを取る。逆はU14のtensorの後の制限。
元のU14のthick生成・compact生成仮定を保持する。
-/

@[expose] public section QuasiEquivalenceEndomorphismComparison
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)
  (hF : QuasiEquivalence F) (G : PerfectDGModule A E)
  (hgen : endomorphismThickGeneratesPerfect A E Set.univ G)

local instance moritaQuasiEquivalenceEndomorphismComparisonLocal1 :
    (dgDerivedExtension A D E F).CommShift ℤ := dgDerivedExtensionCommShift A D E F
local instance moritaQuasiEquivalenceEndomorphismComparisonLocal2 :
    (dgDerivedRestriction A D E F).CommShift ℤ := dgDerivedRestrictionCommShift A D E F
local instance moritaQuasiEquivalenceEndomorphismComparisonLocal3 :
    (quasiEquivalencePerfectExtension A D E F).CommShift ℤ :=
  quasiEquivalencePerfectExtensionCommShift A D E F
local instance moritaQuasiEquivalenceEndomorphismComparisonLocal4 :
    (quasiEquivalencePerfectRestriction A D E F hF).CommShift ℤ :=
  quasiEquivalencePerfectRestrictionCommShift A D E F hF
local instance moritaQuasiEquivalenceEndomorphismComparisonLocal5 :
    (quasiEquivalencePerfectEquivalence A D E F hF).functor.CommShift ℤ :=
  quasiEquivalencePerfectExtensionCommShift A D E F
local instance moritaQuasiEquivalenceEndomorphismComparisonLocal6 :
    (endomorphismDerivedHom A E G.val G.property.1).CommShift ℤ :=
  endomorphismDerivedHomCommShift A E G.val G.property.1
local instance moritaQuasiEquivalenceEndomorphismComparisonLocal7 :
    (endomorphismDerivedTensor A E G.val).CommShift ℤ :=
  endomorphismDerivedTensorCommShift A E G.val G.property.1
local instance moritaQuasiEquivalenceEndomorphismComparisonLocal8 :
    (perfectEndomorphismHomToPerfect A E Set.univ G hgen).CommShift ℤ :=
  perfectEndomorphismHomCommShift A E Set.univ G hgen
local instance moritaQuasiEquivalenceEndomorphismComparisonLocal9 :
    (perfectEndomorphismEquivalence A E Set.univ G hgen).functor.CommShift ℤ :=
  perfectEndomorphismHomCommShift A E Set.univ G hgen
local instance moritaQuasiEquivalenceEndomorphismComparisonLocal10 :
    (perfectEndomorphismTensorToPerfect A E Set.univ G).CommShift ℤ :=
  perfectEndomorphismTensorCommShift A E Set.univ G

def quasiEquivalenceEndomorphismPerfectEquivalence :
    PerfectModuleCategory A D ≌ PerfectModuleCategory A (EndomorphismObject G.val) :=
  (quasiEquivalencePerfectEquivalence A D E F hF).trans
    (perfectEndomorphismEquivalence A E Set.univ G hgen)

instance quasiEquivalenceEndomorphismPerfectFunctorCommShift :
    (quasiEquivalenceEndomorphismPerfectEquivalence A D E F hF G hgen).functor.CommShift ℤ := by
  change (quasiEquivalencePerfectExtension A D E F ⋙
    perfectEndomorphismHomToPerfect A E Set.univ G hgen).CommShift ℤ
  infer_instance

lemma quasiEquivalenceEndomorphismPerfectFunctorIsTriangulated :
    (quasiEquivalenceEndomorphismPerfectEquivalence A D E F hF G hgen).functor.IsTriangulated := by
  let := quasiEquivalencePerfectExtensionIsTriangulated A D E F
  let := perfectEndomorphismHomIsTriangulated A E Set.univ G hgen
  change (quasiEquivalencePerfectExtension A D E F ⋙
    perfectEndomorphismHomToPerfect A E Set.univ G hgen).IsTriangulated
  infer_instance

def quasiEquivalenceEndomorphismPerfectHomSquare :
    (quasiEquivalenceEndomorphismPerfectEquivalence A D E F hF G hgen).functor ⋙
        perfectModuleInclusion A (EndomorphismObject G.val) Set.univ ≅
      perfectModuleInclusion A D Set.univ ⋙
        (dgDerivedExtension A D E F ⋙ endomorphismDerivedHom A E G.val G.property.1) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (perfectEndomorphismHomInclusionIso A E Set.univ G hgen) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (quasiEquivalencePerfectExtensionInclusionIso A D E F) _ ≪≫
    Functor.associator _ _ _

lemma quasiEquivalenceEndomorphismPerfectHomSquareCommShift :
    NatTrans.CommShift
      (quasiEquivalenceEndomorphismPerfectHomSquare A D E F hF G hgen).hom ℤ := by
  let := perfectEndomorphismHomInclusionIso_commShift A E Set.univ G hgen
  let := quasiEquivalencePerfectExtensionInclusionCommShift A D E F
  dsimp only [quasiEquivalenceEndomorphismPerfectHomSquare, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
  infer_instance

def quasiEquivalenceEndomorphismPerfectHomTriangleSquare :
    (quasiEquivalenceEndomorphismPerfectEquivalence A D E F hF G hgen).functor.mapTriangle ⋙
        (perfectModuleInclusion A (EndomorphismObject G.val) Set.univ).mapTriangle ≅
      (perfectModuleInclusion A D Set.univ).mapTriangle ⋙
        (dgDerivedExtension A D E F ⋙
          endomorphismDerivedHom A E G.val G.property.1).mapTriangle := by
  let := quasiEquivalenceEndomorphismPerfectHomSquareCommShift A D E F hF G hgen
  exact (Functor.mapTriangleCompIso _ _).symm ≪≫
    Functor.mapTriangleIso (quasiEquivalenceEndomorphismPerfectHomSquare A D E F hF G hgen) ≪≫
    Functor.mapTriangleCompIso _ _

/-- 合成同値の逆は、元のU14再構成tensorの後に実際の制限を適用する経路と同型。 -/
def quasiEquivalenceEndomorphismPerfectTensorInverseIso :
    perfectEndomorphismTensorToPerfect A E Set.univ G ⋙
        quasiEquivalencePerfectRestriction A D E F hF ≅
      (quasiEquivalenceEndomorphismPerfectEquivalence A D E F hF G hgen).inverse :=
  Functor.isoWhiskerRight (perfectEndomorphismTensorInverseIso A E Set.univ G hgen) _

def quasiEquivalenceEndomorphismPerfectTensorSquare :
    (perfectEndomorphismTensorToPerfect A E Set.univ G ⋙
        quasiEquivalencePerfectRestriction A D E F hF) ⋙
        perfectModuleInclusion A D Set.univ ≅
      perfectModuleInclusion A (EndomorphismObject G.val) Set.univ ⋙
        (endomorphismDerivedTensor A E G.val ⋙ dgDerivedRestriction A D E F) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (quasiEquivalencePerfectRestrictionInclusionIso A D E F hF) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (perfectEndomorphismTensorInclusionIso A E Set.univ G) _ ≪≫
    Functor.associator _ _ _

omit hgen in
lemma quasiEquivalenceEndomorphismPerfectTensorSquareCommShift :
    NatTrans.CommShift
      (quasiEquivalenceEndomorphismPerfectTensorSquare A D E F hF G).hom ℤ := by
  let := perfectEndomorphismTensorInclusionIso_commShift A E Set.univ G
  let := quasiEquivalencePerfectRestrictionInclusionCommShift A D E F hF
  dsimp only [quasiEquivalenceEndomorphismPerfectTensorSquare, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
  infer_instance

omit hgen in
def quasiEquivalenceEndomorphismPerfectTensorTriangleSquare :
    (perfectEndomorphismTensorToPerfect A E Set.univ G ⋙
        quasiEquivalencePerfectRestriction A D E F hF).mapTriangle ⋙
        (perfectModuleInclusion A D Set.univ).mapTriangle ≅
      (perfectModuleInclusion A (EndomorphismObject G.val) Set.univ).mapTriangle ⋙
        (endomorphismDerivedTensor A E G.val ⋙ dgDerivedRestriction A D E F).mapTriangle := by
  let := quasiEquivalenceEndomorphismPerfectTensorSquareCommShift A D E F hF G
  exact (Functor.mapTriangleCompIso _ _).symm ≪≫
    Functor.mapTriangleIso (quasiEquivalenceEndomorphismPerfectTensorSquare A D E F hF G) ≪≫
    Functor.mapTriangleCompIso _ _

variable (hCG : endomorphismCompactGenerator A E G.val)

/-- U14cの全導来同値との合成。compact生成仮定を省略しない。 -/
def quasiEquivalenceEndomorphismDerivedEquivalence :
    DerivedModuleCategory A D ≌ DerivedModuleCategory A (EndomorphismObject G.val) :=
  (dgFunctorDerivedEquivalence A D E F hF).trans
    (endomorphismDerivedEquivalence_ofCompactGenerator A E Set.univ G hgen hCG).symm

lemma quasiEquivalenceEndomorphismDerivedEquivalence_functor :
    (quasiEquivalenceEndomorphismDerivedEquivalence A D E F hF G hgen hCG).functor =
      dgDerivedExtension A D E F ⋙ endomorphismDerivedHom A E G.val G.property.1 := rfl

lemma quasiEquivalenceEndomorphismDerivedEquivalence_inverse :
    (quasiEquivalenceEndomorphismDerivedEquivalence A D E F hF G hgen hCG).inverse =
      endomorphismDerivedTensor A E G.val ⋙ dgDerivedRestriction A D E F := rfl

def quasiEquivalenceEndomorphismDerivedPerfectSquare :
    (quasiEquivalenceEndomorphismPerfectEquivalence A D E F hF G hgen).functor ⋙
        perfectModuleInclusion A (EndomorphismObject G.val) Set.univ ≅
      perfectModuleInclusion A D Set.univ ⋙
        (quasiEquivalenceEndomorphismDerivedEquivalence A D E F hF G hgen hCG).functor :=
  quasiEquivalenceEndomorphismPerfectHomSquare A D E F hF G hgen

end SerrePositivity.DifferentialGraded
end

end QuasiEquivalenceEndomorphismComparison
