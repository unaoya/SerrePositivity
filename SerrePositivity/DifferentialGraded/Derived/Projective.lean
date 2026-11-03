module

public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import SerrePositivity.DifferentialGraded.Complexes.TensorShift
public import Mathlib.CategoryTheory.HomCongr
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.CategoryTheory.Localization.Opposite
public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# Derived.Projective

## 概要
17 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## ProjectiveHomQuasiIso（旧 SerrePositivity/DifferentialGraded/Derived/ProjectiveHomQuasiIso.lean） -/

/-! # 射影的始域からの全Homは指定quasiIsoを保つ -/

@[expose] public section ProjectiveHomQuasiIso
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleHomotopicallyProjective_postcompose_quasiIso {T M N : ModuleCategory A D}
    (hT : moduleHomotopicallyProjective A D T) (f : M ⟶ N)
    (hf : moduleQuasiIso A D f) : QuasiIso (eHomWhiskerLeft (Complex A) T f) := by
  apply (complex_quasiIso_iff_acyclic_cone A _).2
  intro q
  exact (hT (moduleCone A D f) ((moduleQuasiIso_iff_acyclic_cone A D f).1 hf) q).of_iso
    (moduleHomConeIso A D T f).symm

lemma moduleSemifree_postcompose_quasiIso {T M N : ModuleCategory A D}
    (hT : moduleSemifree A D T) (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    QuasiIso (eHomWhiskerLeft (Complex A) T f) :=
  moduleHomotopicallyProjective_postcompose_quasiIso A D
    (moduleSemifree_homotopicallyProjective A D hT) f hf

end SerrePositivity.DifferentialGraded
end

end ProjectiveHomQuasiIso

/-! ## ProjectiveHomotopyLifting（旧 SerrePositivity/DifferentialGraded/Derived/ProjectiveHomotopyLifting.lean） -/

/-! # 射影的始域からquasiIsoに沿うホモトピーまでの持ち上げと一意性 -/

@[expose] public section ProjectiveHomotopyLifting
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleHomotopicallyProjective_homotopy_lift {T M N : ModuleCategory A D}
    (hT : moduleHomotopicallyProjective A D T) (f : M ⟶ N)
    (hf : moduleQuasiIso A D f) (g : T ⟶ N) :
    ∃ s : T ⟶ M, Nonempty (ModuleHomotopy A D (s ≫ f) g) := by
  let K := moduleHom A D (ForgetEnrichment.to (Complex A) T)
    (ForgetEnrichment.to (Complex A) M)
  let L := moduleHom A D (ForgetEnrichment.to (Complex A) T)
    (ForgetEnrichment.to (Complex A) N)
  let r : K ⟶ L := eHomWhiskerLeft (Complex A) T f
  have hr : QuasiIso r := moduleHomotopicallyProjective_postcompose_quasiIso A D hT f hf
  let z := cycleFromUnit L (ForgetEnrichment.homTo (Complex A) g)
  have hl := complexQuasiIso_cycle_lift (K := K) (L := L) A r hr (-1)
  rw [show (-1 : ℤ) + 1 = 0 by omega, show (0 : ℤ) + 1 = 1 by omega] at hl
  obtain ⟨a, ha, b, hb⟩ := hl z.val z.property
  let s : T ⟶ M := moduleMorphismOfCycle A D a ha
  have hsf : r.f 0 a =
      (cycleFromUnit L (ForgetEnrichment.homTo (Complex A) (s ≫ f))).val := by
    calc
      r.f 0 a = r.f 0
          (cycleFromUnit K (ForgetEnrichment.homTo (Complex A) s)).val :=
        congrArg (r.f 0) (moduleMorphismOfCycle_cycle A D (M := T) (N := M) a ha).symm
      _ = _ := moduleHomCycle_postcompose A D s f
  refine ⟨s, ⟨⟨-b, ?_⟩⟩⟩
  change L.d (-1) 0 (-b) =
    (cycleFromUnit L (ForgetEnrichment.homTo (Complex A) (s ≫ f))).val - z.val
  rw [map_neg, hb, hsf, neg_sub]

lemma moduleHomotopicallyProjective_homotopy_reflect {T M N : ModuleCategory A D}
    (hT : moduleHomotopicallyProjective A D T) (f : M ⟶ N)
    (hf : moduleQuasiIso A D f) (s t : T ⟶ M)
    (h : ModuleHomotopy A D (s ≫ f) (t ≫ f)) : Nonempty (ModuleHomotopy A D s t) := by
  let K := moduleHom A D (ForgetEnrichment.to (Complex A) T)
    (ForgetEnrichment.to (Complex A) M)
  let L := moduleHom A D (ForgetEnrichment.to (Complex A) T)
    (ForgetEnrichment.to (Complex A) N)
  let r : K ⟶ L := eHomWhiskerLeft (Complex A) T f
  have hr : QuasiIso r := moduleHomotopicallyProjective_postcompose_quasiIso A D hT f hf
  let zs := cycleFromUnit K (ForgetEnrichment.homTo (Complex A) s)
  let zt := cycleFromUnit K (ForgetEnrichment.homTo (Complex A) t)
  let a := zs.val - zt.val
  have ha : K.d 0 1 a = 0 := by rw [map_sub, zs.property, zt.property, sub_self]
  have hs : r.f 0 zs.val =
      (cycleFromUnit L (ForgetEnrichment.homTo (Complex A) (s ≫ f))).val :=
    moduleHomCycle_postcompose A D s f
  have ht : r.f 0 zt.val =
      (cycleFromUnit L (ForgetEnrichment.homTo (Complex A) (t ≫ f))).val :=
    moduleHomCycle_postcompose A D t f
  have hb : L.d (-1) 0 h.val = r.f 0 a := by
    calc
      L.d (-1) 0 h.val =
          (cycleFromUnit L (ForgetEnrichment.homTo (Complex A) (s ≫ f))).val -
            (cycleFromUnit L (ForgetEnrichment.homTo (Complex A) (t ≫ f))).val := h.property
      _ = r.f 0 zs.val - r.f 0 zt.val := congrArg₂ (fun x y : L.X 0 => x - y) hs.symm ht.symm
      _ = r.f 0 a := (map_sub _ _ _).symm
  have hl := complexQuasiIso_boundary_reflect (K := K) (L := L) A r hr (-1)
  rw [show (-1 : ℤ) + 1 = 0 by omega, show (0 : ℤ) + 1 = 1 by omega] at hl
  obtain ⟨u, hu⟩ := hl a ha h.val hb
  exact ⟨⟨u, hu⟩⟩

end SerrePositivity.DifferentialGraded
end

end ProjectiveHomotopyLifting

/-! ## ProjectiveHomotopyHom（旧 SerrePositivity/DifferentialGraded/Derived/ProjectiveHomotopyHom.lean） -/

/-! # 射影的始域からのK(D)のHomとquasiIso

準同型の後合成は全単射であり、射影的対象間の準同型はK(D)で同型となる。
-/

@[expose] public section ProjectiveHomotopyHom
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleHomotopicallyProjective_postcompose_map_eq_iff {T M N : ModuleCategory A D}
    (hT : moduleHomotopicallyProjective A D T) (f : M ⟶ N)
    (hf : moduleQuasiIso A D f) (s t : T ⟶ M) :
    (moduleToHomotopy A D).map (s ≫ f) = (moduleToHomotopy A D).map (t ≫ f) ↔
      (moduleToHomotopy A D).map s = (moduleToHomotopy A D).map t := by
  constructor
  · intro h
    obtain ⟨h⟩ := (moduleToHomotopy_map_eq_iff A D _ _).1 h
    exact (moduleToHomotopy_map_eq_iff A D s t).2
      (moduleHomotopicallyProjective_homotopy_reflect A D hT f hf s t h)
  · intro h
    simpa only [CategoryTheory.Functor.map_comp] using
      congrArg (fun a => a ≫ (moduleToHomotopy A D).map f) h

lemma moduleHomotopicallyProjective_homotopy_postcompose_bijective
    {T M N : ModuleCategory A D} (hT : moduleHomotopicallyProjective A D T)
    (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    Function.Bijective (fun s : (moduleToHomotopy A D).obj T ⟶ (moduleToHomotopy A D).obj M =>
      s ≫ (moduleToHomotopy A D).map f) := by
  constructor
  · intro s t h
    obtain ⟨s, rfl⟩ := (moduleToHomotopy A D).map_surjective s
    obtain ⟨t, rfl⟩ := (moduleToHomotopy A D).map_surjective t
    apply (moduleHomotopicallyProjective_postcompose_map_eq_iff A D hT f hf s t).1
    simpa only [CategoryTheory.Functor.map_comp] using h
  · intro g
    obtain ⟨g, rfl⟩ := (moduleToHomotopy A D).map_surjective g
    obtain ⟨s, hs⟩ := moduleHomotopicallyProjective_homotopy_lift A D hT f hf g
    refine ⟨(moduleToHomotopy A D).map s, ?_⟩
    dsimp only
    rw [← CategoryTheory.Functor.map_comp]
    exact (moduleToHomotopy_map_eq_iff A D _ _).2 hs

lemma moduleHomotopicallyProjective_quasiIso_isIso_homotopy
    {M N : ModuleCategory A D} (hM : moduleHomotopicallyProjective A D M)
    (hN : moduleHomotopicallyProjective A D N) (f : M ⟶ N)
    (hf : moduleQuasiIso A D f) : IsIso ((moduleToHomotopy A D).map f) := by
  obtain ⟨s, hs⟩ := moduleHomotopicallyProjective_homotopy_lift A D hN f hf (𝟙 N)
  have hs' : (moduleToHomotopy A D).map s ≫ (moduleToHomotopy A D).map f = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp]
    exact ((moduleToHomotopy_map_eq_iff A D _ _).2 hs).trans
      ((moduleToHomotopy A D).map_id N)
  have ht : (moduleToHomotopy A D).map f ≫ (moduleToHomotopy A D).map s = 𝟙 _ := by
    apply (moduleHomotopicallyProjective_homotopy_postcompose_bijective A D hM f hf).1
    dsimp only
    rw [Category.assoc, hs', Category.comp_id, Category.id_comp]
  exact ⟨⟨(moduleToHomotopy A D).map s, ht, hs'⟩⟩

end SerrePositivity.DifferentialGraded
end

end ProjectiveHomotopyHom

/-! ## ProjectivePrecomposition（旧 SerrePositivity/DifferentialGraded/Derived/ProjectivePrecomposition.lean） -/

/-! # 射影的対象間のquasiIsoによる前合成はHom複体のホモトピー同値 -/

@[expose] public section ProjectivePrecomposition
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleProjectivePrecomposeHomotopyEquiv {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    (f : M ⟶ N) (hf : moduleQuasiIso A D f) (T : ModuleCategory A D) :
    HomotopyEquiv (N ⟶[Complex A] T) (M ⟶[Complex A] T) := by
  let Q := moduleToHomotopy A D
  let : IsIso (Q.map f) := moduleHomotopicallyProjective_quasiIso_isIso_homotopy A D hM hN f hf
  let g : N ⟶ M := Q.preimage (inv (Q.map f))
  have hg : Q.map g = inv (Q.map f) := Q.map_preimage _
  have hgf : Nonempty (ModuleHomotopy A D (g ≫ f) (𝟙 N)) := by
    apply (moduleToHomotopy_map_eq_iff A D _ _).1
    change Q.map (g ≫ f) = Q.map (𝟙 N)
    rw [CategoryTheory.Functor.map_comp, hg, IsIso.inv_hom_id, CategoryTheory.Functor.map_id]
  have hfg : Nonempty (ModuleHomotopy A D (f ≫ g) (𝟙 M)) := by
    apply (moduleToHomotopy_map_eq_iff A D _ _).1
    change Q.map (f ≫ g) = Q.map (𝟙 M)
    rw [CategoryTheory.Functor.map_comp, hg, IsIso.hom_inv_id, CategoryTheory.Functor.map_id]
  refine
    { hom := eHomWhiskerRight (Complex A) f T
      inv := eHomWhiskerRight (Complex A) g T
      homotopyHomInvId := ?_
      homotopyInvHomId := ?_ }
  · simpa only [eHomWhiskerRight_comp, eHomWhiskerRight_id] using
      moduleHomPrecomposeHomotopy A D hgf.some T
  · simpa only [eHomWhiskerRight_comp, eHomWhiskerRight_id] using
      moduleHomPrecomposeHomotopy A D hfg.some T

lemma moduleHomotopicallyProjective_precompose_quasiIso {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    (f : M ⟶ N) (hf : moduleQuasiIso A D f) (T : ModuleCategory A D) :
    QuasiIso (eHomWhiskerRight (Complex A) f T) :=
  (moduleProjectivePrecomposeHomotopyEquiv A D hM hN f hf T).quasiIso_hom

end SerrePositivity.DifferentialGraded
end

end ProjectivePrecomposition

/-! ## ProjectiveLocalizationHom（旧 SerrePositivity/DifferentialGraded/Derived/ProjectiveLocalizationHom.lean） -/

/-! # 射影的始域に対する局所化のHom計算 -/

@[expose] public section ProjectiveLocalizationHom
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleHomotopicallyProjective_coyoneda_inverts {P : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P) :
    (moduleHomotopyQuasiIso A D).IsInvertedBy
      (coyoneda.obj (op ((moduleToHomotopy A D).obj P))) := by
  intro M N f hf
  obtain ⟨M⟩ := M
  obtain ⟨N⟩ := N
  obtain ⟨g, rfl⟩ := (moduleToHomotopy A D).map_surjective f
  apply (CategoryTheory.isIso_iff_bijective _).2
  exact moduleHomotopicallyProjective_homotopy_postcompose_bijective A D hP g
    ((moduleHomotopyQuasiIso_map_iff A D g).1 hf)

/-- 射影的始域のK(D)のHomを指定D(D)のHomと同定する。 -/
def moduleProjectiveLocalizationHomEquiv {P : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P) (N : ModuleHomotopyCategory A D) :
    ((moduleToHomotopy A D).obj P ⟶ N) ≃
      ((moduleHomotopyToDerivedClosed A D).obj ((moduleToHomotopy A D).obj P) ⟶
        (moduleHomotopyToDerivedClosed A D).obj N) :=
  LocalizationHom.mapEquiv (moduleHomotopyQuasiIso A D)
    (moduleHomotopyToDerivedClosed A D) _
    (moduleHomotopicallyProjective_coyoneda_inverts A D hP) N

lemma moduleProjectiveLocalizationHomEquiv_apply {P : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P) {N : ModuleHomotopyCategory A D}
    (f : (moduleToHomotopy A D).obj P ⟶ N) :
    moduleProjectiveLocalizationHomEquiv A D hP N f =
      (moduleHomotopyToDerivedClosed A D).map f :=
  LocalizationHom.mapEquiv_apply _ _ _ _ _ _

lemma moduleProjectiveLocalization_map_bijective {P : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P) (N : ModuleHomotopyCategory A D) :
    Function.Bijective ((moduleHomotopyToDerivedClosed A D).map
      (X := (moduleToHomotopy A D).obj P) (Y := N)) :=
  LocalizationHom.map_bijective _ _ _
    (moduleHomotopicallyProjective_coyoneda_inverts A D hP) N


/-- 主局所化関手を用いた射影的始域のHom計算。 -/
def moduleProjectiveDerivedHomEquiv {P : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P) (N : ModuleCategory A D) :
    ((moduleToHomotopy A D).obj P ⟶ (moduleToHomotopy A D).obj N) ≃
      ((moduleToDerived A D).obj P ⟶ (moduleToDerived A D).obj N) :=
  (moduleProjectiveLocalizationHomEquiv A D hP ((moduleToHomotopy A D).obj N)).trans
    (Iso.homCongr ((moduleToHomotopyDerivedIso A D).app P)
      ((moduleToHomotopyDerivedIso A D).app N))

lemma moduleProjectiveDerivedHomEquiv_map {P N : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P) (f : P ⟶ N) :
    moduleProjectiveDerivedHomEquiv A D hP N ((moduleToHomotopy A D).map f) =
      (moduleToDerived A D).map f := by
  change ((moduleToHomotopyDerivedIso A D).app P).inv ≫
    moduleProjectiveLocalizationHomEquiv A D hP _ ((moduleToHomotopy A D).map f) ≫
      ((moduleToHomotopyDerivedIso A D).app N).hom = _
  rw [moduleProjectiveLocalizationHomEquiv_apply]
  have h := (moduleToHomotopyDerivedIso A D).hom.naturality f
  change (moduleHomotopyToDerivedClosed A D).map ((moduleToHomotopy A D).map f) ≫
    ((moduleToHomotopyDerivedIso A D).app N).hom =
      ((moduleToHomotopyDerivedIso A D).app P).hom ≫ (moduleToDerived A D).map f at h
  rw [h, Iso.inv_hom_id_assoc]

end SerrePositivity.DifferentialGraded
end

end ProjectiveLocalizationHom

/-! ## ProjectiveDerivedLifting（旧 SerrePositivity/DifferentialGraded/Derived/ProjectiveDerivedLifting.lean） -/

/-! # 射影的始域の導来射を実際の加群射へ持ち上げる -/

@[expose] public section ProjectiveDerivedLifting
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleProjectiveToDerived_map_surjective {P N : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P) :
    Function.Surjective ((moduleToDerived A D).map (X := P) (Y := N)) := by
  intro f
  obtain ⟨g, hg⟩ := (moduleToHomotopy A D).map_surjective
    ((moduleProjectiveDerivedHomEquiv A D hP N).symm f)
  refine ⟨g, ?_⟩
  rw [← moduleProjectiveDerivedHomEquiv_map A D hP, hg, Equiv.apply_symm_apply]

end SerrePositivity.DifferentialGraded
end

end ProjectiveDerivedLifting

/-! ## HomOut（旧 SerrePositivity/DifferentialGraded/Derived/HomOut.lean） -/

/-! # 射影的始域からの全Homの指定導来局所化への延長

値域は宇宙wを指定した既存D(A)。始域変数の選択独立性は後続で扱う。
-/

@[expose] public section HomOut
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

def moduleHomOutToDerived (T : ModuleCategory A D) :
    ModuleCategory A D ⥤ DerivedCategory (ModuleCat A) :=
  eCoyoneda (Complex A) T ⋙ DerivedCategory.Q

lemma moduleHomOutToDerived_inverts (T : ModuleCategory A D)
    (hT : moduleHomotopicallyProjective A D T) :
    (moduleQuasiIso A D).IsInvertedBy (moduleHomOutToDerived A D T) := by
  intro M N f hf
  have : QuasiIso (eHomWhiskerLeft (Complex A) T f) :=
    moduleHomotopicallyProjective_postcompose_quasiIso A D hT f hf
  change IsIso (DerivedCategory.Q.map (eHomWhiskerLeft (Complex A) T f))
  infer_instance

def moduleDerivedHomOut (T : ModuleCategory A D) (hT : moduleHomotopicallyProjective A D T) :
    DerivedModuleCategory A D ⥤ DerivedCategory (ModuleCat A) :=
  moduleDerivedLift A D (moduleHomOutToDerived A D T) (moduleHomOutToDerived_inverts A D T hT)

lemma moduleDerivedHomOut_fac (T : ModuleCategory A D)
    (hT : moduleHomotopicallyProjective A D T) :
    moduleToDerived A D ⋙ moduleDerivedHomOut A D T hT = moduleHomOutToDerived A D T :=
  moduleDerivedLift_fac A D _ _

def moduleDerivedHomOutComputation (T : ModuleCategory A D)
    (hT : moduleHomotopicallyProjective A D T) (N : ModuleCategory A D) :
    (moduleDerivedHomOut A D T hT).obj ((moduleToDerived A D).obj N) ≅
      DerivedCategory.Q.obj (moduleHom A D (ForgetEnrichment.to (Complex A) T)
        (ForgetEnrichment.to (Complex A) N)) :=
  eqToIso (congrArg (fun F => F.obj N) (moduleDerivedHomOut_fac A D T hT))

def moduleResolvedHomOut (M : ModuleCategory A D) :
    DerivedModuleCategory A D ⥤ DerivedCategory (ModuleCat A) :=
  moduleDerivedHomOut A D (moduleResolutionCandidate A D M)
    (moduleSemifree_homotopicallyProjective A D (moduleResolutionCandidate_semifree A D M))

end SerrePositivity.DifferentialGraded
end

end HomOut

/-! ## HomOutPrecomposition（旧 SerrePositivity/DifferentialGraded/Derived/HomOutPrecomposition.lean） -/

/-! # 射影的始域の射による導来Hom関手間の自然変換

全Homの前合成を指定局所化で延長し、合成・ホモトピーとの整合性を証明する。
-/

@[expose] public section HomOutPrecomposition
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- 豊穣Homの表記で計算する同型。主Hom endと同じMathlib豊穣構造を使う。 -/
def moduleDerivedHomOutEnrichedComputation (T : ModuleCategory A D)
    (hT : moduleHomotopicallyProjective A D T) (N : ModuleCategory A D) :
    (moduleDerivedHomOut A D T hT).obj ((moduleToDerived A D).obj N) ≅
      DerivedCategory.Q.obj (T ⟶[Complex A] N) :=
  eqToIso (congrArg (fun F => F.obj N) (moduleDerivedHomOut_fac A D T hT))

def moduleHomOutToDerivedPrecomp {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleHomOutToDerived A D N ⟶ moduleHomOutToDerived A D M :=
  Functor.whiskerRight ((eHomFunctor (Complex A) (ModuleCategory A D)).map f.op) DerivedCategory.Q

lemma moduleHomOutToDerivedPrecomp_app {M N : ModuleCategory A D} (f : M ⟶ N)
    (T : ModuleCategory A D) :
    (moduleHomOutToDerivedPrecomp A D f).app T =
      DerivedCategory.Q.map (eHomWhiskerRight (Complex A) f T) := rfl

def moduleDerivedHomOutPrecomp {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    (f : M ⟶ N) : moduleDerivedHomOut A D N hN ⟶ moduleDerivedHomOut A D M hM :=
  Localization.Construction.natTransExtension
    (eqToHom (moduleDerivedHomOut_fac A D N hN) ≫ moduleHomOutToDerivedPrecomp A D f ≫
      eqToHom (moduleDerivedHomOut_fac A D M hM).symm)

lemma moduleDerivedHomOutPrecomp_app {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    (f : M ⟶ N) (T : ModuleCategory A D) :
    (moduleDerivedHomOutPrecomp A D hM hN f).app ((moduleToDerived A D).obj T) =
      (moduleDerivedHomOutEnrichedComputation A D N hN T).hom ≫
        DerivedCategory.Q.map (eHomWhiskerRight (Complex A) f T) ≫
          (moduleDerivedHomOutEnrichedComputation A D M hM T).inv := by
  simp only [moduleDerivedHomOutPrecomp, Localization.Construction.natTransExtension_app,
    Localization.Construction.NatTransExtension.app_eq, NatTrans.comp_app, eqToHom_app]
  rfl

lemma moduleDerivedHomOutPrecomp_id (M : ModuleCategory A D)
    (hM : moduleHomotopicallyProjective A D M) :
    moduleDerivedHomOutPrecomp A D hM hM (𝟙 M) = 𝟙 _ := by
  apply moduleDerivedNatTrans_ext A D
  intro T
  rw [moduleDerivedHomOutPrecomp_app, eHomWhiskerRight_id, CategoryTheory.Functor.map_id]
  simp

lemma moduleDerivedHomOutPrecomp_comp {M N P : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    (hP : moduleHomotopicallyProjective A D P) (f : M ⟶ N) (g : N ⟶ P) :
    moduleDerivedHomOutPrecomp A D hM hP (f ≫ g) =
      moduleDerivedHomOutPrecomp A D hN hP g ≫ moduleDerivedHomOutPrecomp A D hM hN f := by
  apply moduleDerivedNatTrans_ext A D
  intro T
  rw [NatTrans.comp_app, moduleDerivedHomOutPrecomp_app, moduleDerivedHomOutPrecomp_app,
    moduleDerivedHomOutPrecomp_app, eHomWhiskerRight_comp, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

lemma moduleDerivedHomOutPrecomp_eq_of_homotopy {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    {f g : M ⟶ N} (h : ModuleHomotopy A D f g) :
    moduleDerivedHomOutPrecomp A D hM hN f = moduleDerivedHomOutPrecomp A D hM hN g := by
  apply moduleDerivedNatTrans_ext A D
  intro T
  rw [moduleDerivedHomOutPrecomp_app, moduleDerivedHomOutPrecomp_app,
    DerivedCategory.Q_map_eq_of_homotopy (ModuleCat A) (moduleHomPrecomposeHomotopy A D h T)]

lemma moduleDerivedHomOutPrecomp_eq_of_homotopy_map_eq {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    {f g : M ⟶ N} (h : (moduleToHomotopy A D).map f = (moduleToHomotopy A D).map g) :
    moduleDerivedHomOutPrecomp A D hM hN f = moduleDerivedHomOutPrecomp A D hM hN g := by
  obtain ⟨h⟩ := (moduleToHomotopy_map_eq_iff A D f g).1 h
  exact moduleDerivedHomOutPrecomp_eq_of_homotopy A D hM hN h

lemma moduleDerivedHomOutPrecomp_isIso {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    IsIso (moduleDerivedHomOutPrecomp A D hM hN f) := by
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro X
  obtain ⟨T, rfl⟩ := (Localization.Construction.objEquiv (moduleQuasiIso A D)).surjective X
  change IsIso ((moduleDerivedHomOutPrecomp A D hM hN f).app ((moduleToDerived A D).obj T))
  rw [moduleDerivedHomOutPrecomp_app]
  have : QuasiIso (eHomWhiskerRight (Complex A) f T) :=
    moduleHomotopicallyProjective_precompose_quasiIso A D hM hN f hf T
  infer_instance

def moduleDerivedHomOutPrecompIso {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    moduleDerivedHomOut A D N hN ≅ moduleDerivedHomOut A D M hM := by
  let : IsIso (moduleDerivedHomOutPrecomp A D hM hN f) :=
    moduleDerivedHomOutPrecomp_isIso A D hM hN f hf
  exact asIso (moduleDerivedHomOutPrecomp A D hM hN f)

end SerrePositivity.DifferentialGraded
end

end HomOutPrecomposition

/-! ## ResolutionComparison（旧 SerrePositivity/DifferentialGraded/Derived/ResolutionComparison.lean） -/

/-! # 射影解像度の比較とK(D)における選択独立性

比較射は全dg自然なホモトピーまで一意であり、三つの解像度の比較と整合する。
-/

@[expose] public section ResolutionComparison
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

theorem moduleProjectiveResolution_comparison {P Q M : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P) (hQ : moduleHomotopicallyProjective A D Q)
    (p : P ⟶ M) (q : Q ⟶ M) (hp : moduleQuasiIso A D p) (hq : moduleQuasiIso A D q) :
    ∃ s : P ⟶ Q, moduleQuasiIso A D s ∧
      (moduleToHomotopy A D).map s ≫ (moduleToHomotopy A D).map q =
        (moduleToHomotopy A D).map p ∧ IsIso ((moduleToHomotopy A D).map s) := by
  obtain ⟨s, hs⟩ := moduleHomotopicallyProjective_homotopy_lift A D hP q hq p
  have hsK := (moduleToHomotopy_map_eq_iff A D (s ≫ q) p).2 hs
  have hscomp : moduleQuasiIso A D (s ≫ q) := by
    apply (moduleHomotopyQuasiIso_map_iff A D (s ≫ q)).1
    rw [hsK]
    exact (moduleHomotopyQuasiIso_map_iff A D p).2 hp
  have hsW : moduleQuasiIso A D s :=
    (moduleQuasiIso A D).of_postcomp (W' := moduleQuasiIso A D) s q hq hscomp
  refine ⟨s, hsW, ?_, moduleHomotopicallyProjective_quasiIso_isIso_homotopy A D hP hQ s hsW⟩
  exact ((moduleToHomotopy A D).map_comp s q).symm.trans hsK

theorem moduleSemifreeResolution_comparison {P Q M : ModuleCategory A D}
    (hP : moduleSemifree A D P) (hQ : moduleSemifree A D Q)
    (p : P ⟶ M) (q : Q ⟶ M) (hp : moduleQuasiIso A D p) (hq : moduleQuasiIso A D q) :
    ∃ s : P ⟶ Q, moduleQuasiIso A D s ∧
      (moduleToHomotopy A D).map s ≫ (moduleToHomotopy A D).map q =
        (moduleToHomotopy A D).map p ∧ IsIso ((moduleToHomotopy A D).map s) :=
  moduleProjectiveResolution_comparison A D (moduleSemifree_homotopicallyProjective A D hP)
    (moduleSemifree_homotopicallyProjective A D hQ) p q hp hq

lemma moduleProjectiveResolution_comparison_unique {P Q M : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P) (p : P ⟶ M) (q : Q ⟶ M)
    (hq : moduleQuasiIso A D q) (s t : P ⟶ Q)
    (hs : (moduleToHomotopy A D).map s ≫ (moduleToHomotopy A D).map q =
      (moduleToHomotopy A D).map p)
    (ht : (moduleToHomotopy A D).map t ≫ (moduleToHomotopy A D).map q =
      (moduleToHomotopy A D).map p) :
    (moduleToHomotopy A D).map s = (moduleToHomotopy A D).map t :=
  (moduleHomotopicallyProjective_homotopy_postcompose_bijective A D hP q hq).1
    (hs.trans ht.symm)

lemma moduleProjectiveResolution_comparison_cocycle {P Q R M : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P) (p : P ⟶ M) (q : Q ⟶ M) (r : R ⟶ M)
    (hr : moduleQuasiIso A D r) (s : P ⟶ Q) (t : Q ⟶ R) (u : P ⟶ R)
    (hs : (moduleToHomotopy A D).map s ≫ (moduleToHomotopy A D).map q =
      (moduleToHomotopy A D).map p)
    (ht : (moduleToHomotopy A D).map t ≫ (moduleToHomotopy A D).map r =
      (moduleToHomotopy A D).map q)
    (hu : (moduleToHomotopy A D).map u ≫ (moduleToHomotopy A D).map r =
      (moduleToHomotopy A D).map p) :
    (moduleToHomotopy A D).map s ≫ (moduleToHomotopy A D).map t =
      (moduleToHomotopy A D).map u := by
  apply (moduleHomotopicallyProjective_homotopy_postcompose_bijective A D hP r hr).1
  dsimp only
  rw [Category.assoc, ht, hs, hu]

end SerrePositivity.DifferentialGraded
end

end ResolutionComparison

/-! ## ProjectiveResolution（旧 SerrePositivity/DifferentialGraded/Derived/ProjectiveResolution.lean） -/

/-! # 証明付き射影解像度と標準比較

対象・増大射・全Homによる射影性・指定quasiIsoを保持する。
-/

@[expose] public section ProjectiveResolution
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

structure ModuleProjectiveResolution (M : ModuleCategory A D) where
  obj : ModuleCategory A D
  π : obj ⟶ M
  projective : moduleHomotopicallyProjective A D obj
  quasiIso : moduleQuasiIso A D π

def moduleCanonicalProjectiveResolution (M : ModuleCategory A D) :
    ModuleProjectiveResolution A D M where
  obj := moduleResolutionCandidate A D M
  π := moduleResolutionCandidateπ A D M
  projective := moduleSemifree_homotopicallyProjective A D
    (moduleResolutionCandidate_semifree A D M)
  quasiIso := moduleResolutionCandidateπ_quasiIso A D M

namespace ModuleProjectiveResolution
variable {A D} {M : ModuleCategory A D}

def comparison (P Q : ModuleProjectiveResolution A D M) : P.obj ⟶ Q.obj :=
  Classical.choose (moduleProjectiveResolution_comparison A D P.projective Q.projective
    P.π Q.π P.quasiIso Q.quasiIso)

lemma comparison_quasiIso (P Q : ModuleProjectiveResolution A D M) :
    moduleQuasiIso A D (P.comparison Q) :=
  (Classical.choose_spec (moduleProjectiveResolution_comparison A D P.projective Q.projective
    P.π Q.π P.quasiIso Q.quasiIso)).1

lemma comparison_fac (P Q : ModuleProjectiveResolution A D M) :
    (moduleToHomotopy A D).map (P.comparison Q) ≫ (moduleToHomotopy A D).map Q.π =
      (moduleToHomotopy A D).map P.π :=
  (Classical.choose_spec (moduleProjectiveResolution_comparison A D P.projective Q.projective
    P.π Q.π P.quasiIso Q.quasiIso)).2.1

lemma comparison_isIso_homotopy (P Q : ModuleProjectiveResolution A D M) :
    IsIso ((moduleToHomotopy A D).map (P.comparison Q)) :=
  moduleHomotopicallyProjective_quasiIso_isIso_homotopy A D P.projective Q.projective
    (P.comparison Q) (P.comparison_quasiIso Q)

lemma comparison_unique (P Q : ModuleProjectiveResolution A D M) (s : P.obj ⟶ Q.obj)
    (hs : (moduleToHomotopy A D).map s ≫ (moduleToHomotopy A D).map Q.π =
      (moduleToHomotopy A D).map P.π) :
    (moduleToHomotopy A D).map (P.comparison Q) = (moduleToHomotopy A D).map s :=
  moduleProjectiveResolution_comparison_unique A D P.projective P.π Q.π Q.quasiIso
    (P.comparison Q) s (P.comparison_fac Q) hs

lemma comparison_comp (P Q R : ModuleProjectiveResolution A D M) :
    (moduleToHomotopy A D).map (P.comparison Q) ≫
      (moduleToHomotopy A D).map (Q.comparison R) =
        (moduleToHomotopy A D).map (P.comparison R) :=
  moduleProjectiveResolution_comparison_cocycle A D P.projective P.π Q.π R.π R.quasiIso
    (P.comparison Q) (Q.comparison R) (P.comparison R)
    (P.comparison_fac Q) (Q.comparison_fac R) (P.comparison_fac R)

lemma comparison_self (P : ModuleProjectiveResolution A D M) :
    (moduleToHomotopy A D).map (P.comparison P) = 𝟙 _ := by
  have h := P.comparison_unique P (𝟙 P.obj) (by
    rw [CategoryTheory.Functor.map_id, Category.id_comp])
  exact h.trans ((moduleToHomotopy A D).map_id _)

end ModuleProjectiveResolution
end SerrePositivity.DifferentialGraded
end

end ProjectiveResolution

/-! ## ProjectiveResolutionLift（旧 SerrePositivity/DifferentialGraded/Derived/ProjectiveResolutionLift.lean） -/

/-! # 射影解像度への射の持ち上げとK(D)での関手法則 -/

@[expose] public section ProjectiveResolutionLift
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
namespace ModuleProjectiveResolution
variable {M N L : ModuleCategory A D}

def lift (P : ModuleProjectiveResolution A D M) (Q : ModuleProjectiveResolution A D N)
    (f : M ⟶ N) : P.obj ⟶ Q.obj :=
  Classical.choose (moduleHomotopicallyProjective_homotopy_lift A D P.projective
    Q.π Q.quasiIso (P.π ≫ f))

lemma lift_fac (P : ModuleProjectiveResolution A D M) (Q : ModuleProjectiveResolution A D N)
    (f : M ⟶ N) :
    (moduleToHomotopy A D).map (P.lift Q f) ≫ (moduleToHomotopy A D).map Q.π =
      (moduleToHomotopy A D).map P.π ≫ (moduleToHomotopy A D).map f := by
  have h := (Classical.choose_spec (moduleHomotopicallyProjective_homotopy_lift A D P.projective
    Q.π Q.quasiIso (P.π ≫ f)))
  have hK := (moduleToHomotopy_map_eq_iff A D _ _).2 h
  exact ((moduleToHomotopy A D).map_comp _ _).symm.trans
    (hK.trans ((moduleToHomotopy A D).map_comp _ _))

lemma lift_unique (P : ModuleProjectiveResolution A D M)
    (Q : ModuleProjectiveResolution A D N) (f : M ⟶ N) (s : P.obj ⟶ Q.obj)
    (hs : (moduleToHomotopy A D).map s ≫ (moduleToHomotopy A D).map Q.π =
      (moduleToHomotopy A D).map P.π ≫ (moduleToHomotopy A D).map f) :
    (moduleToHomotopy A D).map (P.lift Q f) = (moduleToHomotopy A D).map s :=
  (moduleHomotopicallyProjective_homotopy_postcompose_bijective A D
    P.projective Q.π Q.quasiIso).1 ((P.lift_fac Q f).trans hs.symm)

lemma lift_id (P : ModuleProjectiveResolution A D M) :
    (moduleToHomotopy A D).map (P.lift P (𝟙 M)) = 𝟙 _ := by
  have h := P.lift_unique P (𝟙 M) (𝟙 P.obj) (by
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.comp_id])
  exact h.trans ((moduleToHomotopy A D).map_id _)

lemma lift_comp (P : ModuleProjectiveResolution A D M) (Q : ModuleProjectiveResolution A D N)
    (R : ModuleProjectiveResolution A D L) (f : M ⟶ N) (g : N ⟶ L) :
    (moduleToHomotopy A D).map (P.lift Q f) ≫ (moduleToHomotopy A D).map (Q.lift R g) =
      (moduleToHomotopy A D).map (P.lift R (f ≫ g)) := by
  have hs : (moduleToHomotopy A D).map (P.lift Q f ≫ Q.lift R g) ≫
      (moduleToHomotopy A D).map R.π =
        (moduleToHomotopy A D).map P.π ≫ (moduleToHomotopy A D).map (f ≫ g) := by
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      Category.assoc, Q.lift_fac R g, ← Category.assoc, P.lift_fac Q f, Category.assoc]
  exact ((moduleToHomotopy A D).map_comp _ _).symm.trans
    (P.lift_unique R (f ≫ g) _ hs).symm

lemma lift_quasiIso (P : ModuleProjectiveResolution A D M)
    (Q : ModuleProjectiveResolution A D N) (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    moduleQuasiIso A D (P.lift Q f) := by
  have hK : (moduleToHomotopy A D).map (P.lift Q f ≫ Q.π) =
      (moduleToHomotopy A D).map (P.π ≫ f) :=
    ((moduleToHomotopy A D).map_comp _ _).trans
      ((P.lift_fac Q f).trans ((moduleToHomotopy A D).map_comp _ _).symm)
  have hc : moduleQuasiIso A D (P.lift Q f ≫ Q.π) := by
    apply (moduleHomotopyQuasiIso_map_iff A D _).1
    rw [hK]
    apply (moduleHomotopyQuasiIso_map_iff A D _).2
    exact (moduleQuasiIso A D).comp_mem _ _ P.quasiIso hf
  exact (moduleQuasiIso A D).of_postcomp (W' := moduleQuasiIso A D) _ _ Q.quasiIso hc

lemma lift_id_comparison (P Q : ModuleProjectiveResolution A D M) :
    (moduleToHomotopy A D).map (P.lift Q (𝟙 M)) =
      (moduleToHomotopy A D).map (P.comparison Q) :=
  P.lift_unique Q (𝟙 M) (P.comparison Q) (by
    simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using P.comparison_fac Q)

lemma lift_comparison_naturality (P P' : ModuleProjectiveResolution A D M)
    (Q Q' : ModuleProjectiveResolution A D N) (f : M ⟶ N) :
    (moduleToHomotopy A D).map (P.lift Q f) ≫ (moduleToHomotopy A D).map (Q.comparison Q') =
      (moduleToHomotopy A D).map (P.comparison P') ≫ (moduleToHomotopy A D).map (P'.lift Q' f) := by
  apply (moduleHomotopicallyProjective_homotopy_postcompose_bijective A D
    P.projective Q'.π Q'.quasiIso).1
  dsimp only
  rw [Category.assoc, Q.comparison_fac Q', P.lift_fac Q f,
    Category.assoc, P'.lift_fac Q' f, ← Category.assoc, P.comparison_fac P']

end ModuleProjectiveResolution
end SerrePositivity.DifferentialGraded
end

end ProjectiveResolutionLift

/-! ## HomChoice（旧 SerrePositivity/DifferentialGraded/Derived/HomChoice.lean） -/

/-! # 射影解像度による導来Hom関手の選択独立性

比較の自然同型は、任意の比較射による前合成と一致し、恒等・cocycle条件を満たす。
-/

@[expose] public section HomChoice
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

namespace ModuleProjectiveResolution
variable {A D} {M : ModuleCategory A D}

def derivedHom (P : ModuleProjectiveResolution A D M) :
    DerivedModuleCategory A D ⥤ DerivedCategory (ModuleCat A) :=
  moduleDerivedHomOut A D P.obj P.projective

def derivedHomComputation (P : ModuleProjectiveResolution A D M) (T : ModuleCategory A D) :
    P.derivedHom.obj ((moduleToDerived A D).obj T) ≅
      DerivedCategory.Q.obj (P.obj ⟶[Complex A] T) :=
  moduleDerivedHomOutEnrichedComputation A D P.obj P.projective T

def derivedHomIso (P Q : ModuleProjectiveResolution A D M) : Q.derivedHom ≅ P.derivedHom :=
  moduleDerivedHomOutPrecompIso A D P.projective Q.projective
    (P.comparison Q) (P.comparison_quasiIso Q)

lemma derivedHomIso_app (P Q : ModuleProjectiveResolution A D M) (T : ModuleCategory A D) :
    (P.derivedHomIso Q).hom.app ((moduleToDerived A D).obj T) =
      (Q.derivedHomComputation T).hom ≫
        DerivedCategory.Q.map (eHomWhiskerRight (Complex A) (P.comparison Q) T) ≫
          (P.derivedHomComputation T).inv :=
  moduleDerivedHomOutPrecomp_app A D P.projective Q.projective (P.comparison Q) T

lemma derivedHomIso_hom_eq (P Q : ModuleProjectiveResolution A D M) (s : P.obj ⟶ Q.obj)
    (hs : (moduleToHomotopy A D).map s ≫ (moduleToHomotopy A D).map Q.π =
      (moduleToHomotopy A D).map P.π) :
    (P.derivedHomIso Q).hom = moduleDerivedHomOutPrecomp A D P.projective Q.projective s := by
  change moduleDerivedHomOutPrecomp A D P.projective Q.projective (P.comparison Q) = _
  exact moduleDerivedHomOutPrecomp_eq_of_homotopy_map_eq A D P.projective Q.projective
    (P.comparison_unique Q s hs)

lemma derivedHomIso_self (P : ModuleProjectiveResolution A D M) :
    P.derivedHomIso P = Iso.refl P.derivedHom := by
  apply Iso.ext
  change (P.derivedHomIso P).hom = 𝟙 _
  rw [P.derivedHomIso_hom_eq P (𝟙 P.obj) (by
    rw [CategoryTheory.Functor.map_id, Category.id_comp])]
  exact moduleDerivedHomOutPrecomp_id A D P.obj P.projective

lemma derivedHomIso_trans (P Q R : ModuleProjectiveResolution A D M) :
    Q.derivedHomIso R ≪≫ P.derivedHomIso Q = P.derivedHomIso R := by
  apply Iso.ext
  change moduleDerivedHomOutPrecomp A D Q.projective R.projective (Q.comparison R) ≫
    moduleDerivedHomOutPrecomp A D P.projective Q.projective (P.comparison Q) =
      moduleDerivedHomOutPrecomp A D P.projective R.projective (P.comparison R)
  have hc : (moduleToHomotopy A D).map (P.comparison Q ≫ Q.comparison R) =
      (moduleToHomotopy A D).map (P.comparison R) :=
    ((moduleToHomotopy A D).map_comp _ _).trans (P.comparison_comp Q R)
  have h := moduleDerivedHomOutPrecomp_eq_of_homotopy_map_eq A D P.projective R.projective hc
  rw [moduleDerivedHomOutPrecomp_comp] at h
  exact h

end ModuleProjectiveResolution

lemma moduleCanonicalProjectiveResolution_derivedHom (M : ModuleCategory A D) :
    (moduleCanonicalProjectiveResolution A D M).derivedHom = moduleResolvedHomOut A D M := rfl

end SerrePositivity.DifferentialGraded
end

end HomChoice

/-! ## HomBifunctor（旧 SerrePositivity/DifferentialGraded/Derived/HomBifunctor.lean） -/

/-! # 射影解像度による導来Hom双関手

任意の証明付き解像度族に対して始域の反変関手性を構成し、両変数を指定局所化へ運ぶ。
-/

@[expose] public section HomBifunctor
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

def moduleResolutionHomSourceFunctor
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    (ModuleCategory A D)ᵒᵖ ⥤ (DerivedModuleCategory A D ⥤ DerivedCategory (ModuleCat A)) where
  obj X := (R X.unop).derivedHom
  map {X Y} f := moduleDerivedHomOutPrecomp A D (R Y.unop).projective (R X.unop).projective
    ((R Y.unop).lift (R X.unop) f.unop)
  map_id X := by
    let P := R X.unop
    change moduleDerivedHomOutPrecomp A D P.projective P.projective (P.lift P (𝟙 X.unop)) = 𝟙 _
    calc
      _ = moduleDerivedHomOutPrecomp A D P.projective P.projective (𝟙 P.obj) :=
        moduleDerivedHomOutPrecomp_eq_of_homotopy_map_eq A D P.projective P.projective
          ((P.lift_id).trans ((moduleToHomotopy A D).map_id _).symm)
      _ = _ := moduleDerivedHomOutPrecomp_id A D P.obj P.projective
  map_comp {X Y Z} f g := by
    let P := R Z.unop
    let Q := R Y.unop
    let S := R X.unop
    change moduleDerivedHomOutPrecomp A D P.projective S.projective
      (P.lift S (g.unop ≫ f.unop)) =
        moduleDerivedHomOutPrecomp A D Q.projective S.projective (Q.lift S f.unop) ≫
          moduleDerivedHomOutPrecomp A D P.projective Q.projective (P.lift Q g.unop)
    rw [← moduleDerivedHomOutPrecomp_comp]
    apply moduleDerivedHomOutPrecomp_eq_of_homotopy_map_eq A D P.projective S.projective
    exact (P.lift_comp Q S g.unop f.unop).symm.trans
      ((moduleToHomotopy A D).map_comp _ _).symm

lemma moduleResolutionHomSourceFunctor_inverts
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    (moduleQuasiIso A D).op.IsInvertedBy (moduleResolutionHomSourceFunctor A D R) := by
  intro X Y f hf
  change moduleQuasiIso A D f.unop at hf
  exact moduleDerivedHomOutPrecomp_isIso A D (R Y.unop).projective (R X.unop).projective
    ((R Y.unop).lift (R X.unop) f.unop) ((R Y.unop).lift_quasiIso (R X.unop) f.unop hf)

def moduleResolutionDerivedHomBifunctor
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    (DerivedModuleCategory A D)ᵒᵖ ⥤
      (DerivedModuleCategory A D ⥤ DerivedCategory (ModuleCat A)) :=
  Localization.lift (moduleResolutionHomSourceFunctor A D R)
    (moduleResolutionHomSourceFunctor_inverts A D R) (moduleToDerived A D).op

instance moduleResolutionDerivedHomBifunctor_lifting
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    Localization.Lifting (moduleToDerived A D).op (moduleQuasiIso A D).op
      (moduleResolutionHomSourceFunctor A D R) (moduleResolutionDerivedHomBifunctor A D R) :=
  Localization.liftingLift (moduleResolutionHomSourceFunctor A D R)
    (moduleResolutionHomSourceFunctor_inverts A D R) (moduleToDerived A D).op

def moduleResolutionDerivedHomBifunctor_fac
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    (moduleToDerived A D).op ⋙ moduleResolutionDerivedHomBifunctor A D R ≅
      moduleResolutionHomSourceFunctor A D R :=
  Localization.fac (moduleResolutionHomSourceFunctor A D R)
    (moduleResolutionHomSourceFunctor_inverts A D R) (moduleToDerived A D).op

def moduleResolutionDerivedHomBifunctorComputation
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (M N : ModuleCategory A D) :
    ((moduleResolutionDerivedHomBifunctor A D R).obj (op ((moduleToDerived A D).obj M))).obj
        ((moduleToDerived A D).obj N) ≅
      DerivedCategory.Q.obj ((R M).obj ⟶[Complex A] N) :=
  ((moduleResolutionDerivedHomBifunctor_fac A D R).app (op M)).app
    ((moduleToDerived A D).obj N) ≪≫ (R M).derivedHomComputation N

def moduleDerivedHomBifunctor :
    (DerivedModuleCategory A D)ᵒᵖ ⥤
      (DerivedModuleCategory A D ⥤ DerivedCategory (ModuleCat A)) :=
  moduleResolutionDerivedHomBifunctor A D (moduleCanonicalProjectiveResolution A D)

def moduleDerivedHomBifunctorResolutionComputation {M : ModuleCategory A D}
    (P : ModuleProjectiveResolution A D M) (N : ModuleCategory A D) :
    ((moduleDerivedHomBifunctor A D).obj (op ((moduleToDerived A D).obj M))).obj
        ((moduleToDerived A D).obj N) ≅ DerivedCategory.Q.obj (P.obj ⟶[Complex A] N) :=
  ((moduleResolutionDerivedHomBifunctor_fac A D
    (moduleCanonicalProjectiveResolution A D)).app (op M)).app ((moduleToDerived A D).obj N) ≪≫
      (P.derivedHomIso (moduleCanonicalProjectiveResolution A D M)).app
        ((moduleToDerived A D).obj N) ≪≫ P.derivedHomComputation N

end SerrePositivity.DifferentialGraded
end

end HomBifunctor

/-! ## HomBifunctorChoice（旧 SerrePositivity/DifferentialGraded/Derived/HomBifunctorChoice.lean） -/

/-! # 解像度族を替えた導来Hom双関手の自然同型とcocycle条件 -/

@[expose] public section HomBifunctorChoice
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

def moduleResolutionHomSourceIso
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionHomSourceFunctor A D R ≅ moduleResolutionHomSourceFunctor A D S :=
  NatIso.ofComponents (fun X => (S X.unop).derivedHomIso (R X.unop)) (by
    intro X Y f
    let P := S Y.unop
    let Q := R Y.unop
    let U := S X.unop
    let V := R X.unop
    change moduleDerivedHomOutPrecomp A D Q.projective V.projective (Q.lift V f.unop) ≫
      moduleDerivedHomOutPrecomp A D P.projective Q.projective (P.comparison Q) =
        moduleDerivedHomOutPrecomp A D U.projective V.projective (U.comparison V) ≫
          moduleDerivedHomOutPrecomp A D P.projective U.projective (P.lift U f.unop)
    rw [← moduleDerivedHomOutPrecomp_comp, ← moduleDerivedHomOutPrecomp_comp]
    apply moduleDerivedHomOutPrecomp_eq_of_homotopy_map_eq A D P.projective V.projective
    exact ((moduleToHomotopy A D).map_comp _ _).trans
      ((P.lift_comparison_naturality Q U V f.unop).symm.trans
        ((moduleToHomotopy A D).map_comp _ _).symm))

lemma moduleResolutionHomSourceIso_app
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (X : (ModuleCategory A D)ᵒᵖ) :
    (moduleResolutionHomSourceIso A D R S).app X =
      (S X.unop).derivedHomIso (R X.unop) := rfl

lemma moduleResolutionHomSourceIso_self
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionHomSourceIso A D R R = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  change ((R X.unop).derivedHomIso (R X.unop)).hom = 𝟙 _
  rw [ModuleProjectiveResolution.derivedHomIso_self]
  rfl

lemma moduleResolutionHomSourceIso_trans
    (R S T : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionHomSourceIso A D R S ≪≫ moduleResolutionHomSourceIso A D S T =
      moduleResolutionHomSourceIso A D R T := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  change ((S X.unop).derivedHomIso (R X.unop)).hom ≫
    ((T X.unop).derivedHomIso (S X.unop)).hom =
      ((T X.unop).derivedHomIso (R X.unop)).hom
  exact congrArg Iso.hom ((T X.unop).derivedHomIso_trans (S X.unop) (R X.unop))

def moduleResolutionDerivedHomBifunctorIso
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionDerivedHomBifunctor A D R ≅ moduleResolutionDerivedHomBifunctor A D S :=
  Localization.liftNatIso (moduleToDerived A D).op (moduleQuasiIso A D).op
    (moduleResolutionHomSourceFunctor A D R) (moduleResolutionHomSourceFunctor A D S)
    (moduleResolutionDerivedHomBifunctor A D R) (moduleResolutionDerivedHomBifunctor A D S)
    (moduleResolutionHomSourceIso A D R S)

lemma moduleResolutionDerivedHomBifunctorIso_app
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) (M : ModuleCategory A D) :
    (moduleResolutionDerivedHomBifunctorIso A D R S).hom.app (op ((moduleToDerived A D).obj M)) =
      (moduleResolutionDerivedHomBifunctor_fac A D R).hom.app (op M) ≫
        (moduleResolutionHomSourceIso A D R S).hom.app (op M) ≫
          (moduleResolutionDerivedHomBifunctor_fac A D S).inv.app (op M) :=
  Localization.liftNatTrans_app (moduleToDerived A D).op (moduleQuasiIso A D).op
    (moduleResolutionHomSourceFunctor A D R) (moduleResolutionHomSourceFunctor A D S)
    (moduleResolutionDerivedHomBifunctor A D R) (moduleResolutionDerivedHomBifunctor A D S)
    (moduleResolutionHomSourceIso A D R S).hom (op M)

lemma moduleResolutionDerivedHomBifunctorIso_self
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionDerivedHomBifunctorIso A D R R = Iso.refl _ := by
  apply Iso.ext
  change Localization.liftNatTrans (moduleToDerived A D).op (moduleQuasiIso A D).op
    (moduleResolutionHomSourceFunctor A D R) (moduleResolutionHomSourceFunctor A D R)
    (moduleResolutionDerivedHomBifunctor A D R) (moduleResolutionDerivedHomBifunctor A D R)
    (moduleResolutionHomSourceIso A D R R).hom = 𝟙 _
  rw [moduleResolutionHomSourceIso_self, Iso.refl_hom, Localization.liftNatTrans_id]

lemma moduleResolutionDerivedHomBifunctorIso_trans
    (R S T : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionDerivedHomBifunctorIso A D R S ≪≫
      moduleResolutionDerivedHomBifunctorIso A D S T =
        moduleResolutionDerivedHomBifunctorIso A D R T := by
  apply Iso.ext
  change Localization.liftNatTrans (moduleToDerived A D).op (moduleQuasiIso A D).op
    (moduleResolutionHomSourceFunctor A D R) (moduleResolutionHomSourceFunctor A D S)
    (moduleResolutionDerivedHomBifunctor A D R) (moduleResolutionDerivedHomBifunctor A D S)
    (moduleResolutionHomSourceIso A D R S).hom ≫
      Localization.liftNatTrans (moduleToDerived A D).op (moduleQuasiIso A D).op
        (moduleResolutionHomSourceFunctor A D S) (moduleResolutionHomSourceFunctor A D T)
        (moduleResolutionDerivedHomBifunctor A D S) (moduleResolutionDerivedHomBifunctor A D T)
        (moduleResolutionHomSourceIso A D S T).hom =
    Localization.liftNatTrans (moduleToDerived A D).op (moduleQuasiIso A D).op
      (moduleResolutionHomSourceFunctor A D R) (moduleResolutionHomSourceFunctor A D T)
      (moduleResolutionDerivedHomBifunctor A D R) (moduleResolutionDerivedHomBifunctor A D T)
      (moduleResolutionHomSourceIso A D R T).hom
  rw [Localization.comp_liftNatTrans]
  exact congrArg
    (Localization.liftNatTrans (moduleToDerived A D).op (moduleQuasiIso A D).op
      (moduleResolutionHomSourceFunctor A D R) (moduleResolutionHomSourceFunctor A D T)
      (moduleResolutionDerivedHomBifunctor A D R) (moduleResolutionDerivedHomBifunctor A D T))
    (congrArg Iso.hom (moduleResolutionHomSourceIso_trans A D R S T))

def moduleDerivedHomBifunctorChoiceIso
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleDerivedHomBifunctor A D ≅ moduleResolutionDerivedHomBifunctor A D R :=
  moduleResolutionDerivedHomBifunctorIso A D (moduleCanonicalProjectiveResolution A D) R

end SerrePositivity.DifferentialGraded
end

end HomBifunctorChoice

/-! ## ResolutionHom（旧 SerrePositivity/DifferentialGraded/Derived/ResolutionHom.lean） -/

/-! # 射影解像度による導来圏の射集合と局所小性 -/

@[expose] public section ResolutionHom
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 任意の証明付き射影解像度で実際の導来圏の射集合を計算する。 -/
def moduleResolutionDerivedHomEquiv {M : ModuleCategory A D}
    (P : ModuleProjectiveResolution A D M) (N : ModuleCategory A D) :
    ((moduleToHomotopy A D).obj P.obj ⟶ (moduleToHomotopy A D).obj N) ≃
      ((moduleToDerived A D).obj M ⟶ (moduleToDerived A D).obj N) :=
  (moduleProjectiveDerivedHomEquiv A D P.projective N).trans
    (Iso.homCongr (moduleDerivedIso A D P.π P.quasiIso) (Iso.refl _))

lemma moduleResolutionDerivedHomEquiv_map {M N : ModuleCategory A D}
    (P : ModuleProjectiveResolution A D M) (f : P.obj ⟶ N) :
    moduleResolutionDerivedHomEquiv A D P N ((moduleToHomotopy A D).map f) =
      (moduleDerivedIso A D P.π P.quasiIso).inv ≫ (moduleToDerived A D).map f := by
  change (moduleDerivedIso A D P.π P.quasiIso).inv ≫
    moduleProjectiveDerivedHomEquiv A D P.projective N ((moduleToHomotopy A D).map f) ≫ 𝟙 _ = _
  rw [moduleProjectiveDerivedHomEquiv_map, Category.comp_id]

/-- 任意の導来射は指定解像度の増大射を左分母とするroofで表せる。 -/
lemma moduleResolutionDerivedHom_surjective {M N : ModuleCategory A D}
    (P : ModuleProjectiveResolution A D M)
    (g : (moduleToDerived A D).obj M ⟶ (moduleToDerived A D).obj N) :
    ∃ f : P.obj ⟶ N,
      (moduleDerivedIso A D P.π P.quasiIso).inv ≫ (moduleToDerived A D).map f = g := by
  obtain ⟨f, hf⟩ := (moduleResolutionDerivedHomEquiv A D P N).surjective g
  obtain ⟨f, rfl⟩ := (moduleToHomotopy A D).map_surjective f
  exact ⟨f, (moduleResolutionDerivedHomEquiv_map A D P f).symm.trans hf⟩

lemma moduleResolutionDerivedHom_eq_iff {M N : ModuleCategory A D}
    (P : ModuleProjectiveResolution A D M) (f g : P.obj ⟶ N) :
    (moduleDerivedIso A D P.π P.quasiIso).inv ≫ (moduleToDerived A D).map f =
      (moduleDerivedIso A D P.π P.quasiIso).inv ≫ (moduleToDerived A D).map g ↔
        Nonempty (ModuleHomotopy A D f g) := by
  rw [← moduleResolutionDerivedHomEquiv_map A D P f,
    ← moduleResolutionDerivedHomEquiv_map A D P g,
    (moduleResolutionDerivedHomEquiv A D P N).injective.eq_iff,
    moduleToHomotopy_map_eq_iff]

lemma moduleDerivedHom_small (M N : ModuleCategory A D) :
    Small.{u} ((moduleToDerived A D).obj M ⟶ (moduleToDerived A D).obj N) := by
  exact small_of_surjective
    (moduleResolutionDerivedHomEquiv A D (moduleCanonicalProjectiveResolution A D M) N).surjective

instance moduleDerivedLocallySmall : LocallySmall.{u} (DerivedModuleCategory A D) where
  hom_small M N := by
    obtain ⟨⟨M⟩⟩ := M
    obtain ⟨⟨N⟩⟩ := N
    exact moduleDerivedHom_small A D M N

end SerrePositivity.DifferentialGraded
end

end ResolutionHom

/-! ## ResolutionFunctor（旧 SerrePositivity/DifferentialGraded/Derived/ResolutionFunctor.lean） -/

/-! # 指定局所化からK(D)への射影解像度関手

証明付きの解像度族を選び、射の持ち上げのK(D)での一意性を使って関手化する。
-/

@[expose] public section ResolutionFunctor
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 射影解像度族をK(D)に値を持つ関手として扱う。 -/
def moduleResolutionHomotopyFunctor
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    ModuleCategory A D ⥤ ModuleHomotopyCategory A D where
  obj M := (moduleToHomotopy A D).obj (R M).obj
  map {M N} f := (moduleToHomotopy A D).map ((R M).lift (R N) f)
  map_id M := (R M).lift_id
  map_comp {M N P} f g := ((R M).lift_comp (R N) (R P) f g).symm

lemma moduleResolutionHomotopyFunctor_inverts
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    (moduleQuasiIso A D).IsInvertedBy (moduleResolutionHomotopyFunctor A D R) := by
  intro M N f hf
  exact moduleHomotopicallyProjective_quasiIso_isIso_homotopy A D
    (R M).projective (R N).projective ((R M).lift (R N) f) ((R M).lift_quasiIso (R N) f hf)

/-- 指定quasiIso局所化から主K(D)への射影解像度関手。 -/
def moduleDerivedResolutionFunctor
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    DerivedModuleCategory A D ⥤ ModuleHomotopyCategory A D :=
  Localization.lift (moduleResolutionHomotopyFunctor A D R)
    (moduleResolutionHomotopyFunctor_inverts A D R) (moduleToDerived A D)

instance moduleDerivedResolutionFunctor_lifting
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    Localization.Lifting (moduleToDerived A D) (moduleQuasiIso A D)
      (moduleResolutionHomotopyFunctor A D R) (moduleDerivedResolutionFunctor A D R) :=
  Localization.liftingLift (moduleResolutionHomotopyFunctor A D R)
    (moduleResolutionHomotopyFunctor_inverts A D R) (moduleToDerived A D)

def moduleDerivedResolutionFunctor_fac
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleToDerived A D ⋙ moduleDerivedResolutionFunctor A D R ≅
      moduleResolutionHomotopyFunctor A D R :=
  Localization.fac (moduleResolutionHomotopyFunctor A D R)
    (moduleResolutionHomotopyFunctor_inverts A D R) (moduleToDerived A D)

def moduleDerivedResolutionComputation
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) (M : ModuleCategory A D) :
    (moduleDerivedResolutionFunctor A D R).obj ((moduleToDerived A D).obj M) ≅
      (moduleToHomotopy A D).obj (R M).obj :=
  (moduleDerivedResolutionFunctor_fac A D R).app M

end SerrePositivity.DifferentialGraded
end

end ResolutionFunctor

/-! ## ResolutionFunctorChoice（旧 SerrePositivity/DifferentialGraded/Derived/ResolutionFunctorChoice.lean） -/

/-! # 射影解像度関手の選択独立性 -/

@[expose] public section ResolutionFunctorChoice
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleResolutionHomotopyIso
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionHomotopyFunctor A D R ≅ moduleResolutionHomotopyFunctor A D S :=
  NatIso.ofComponents (fun M => by
    have := (R M).comparison_isIso_homotopy (S M)
    exact asIso ((moduleToHomotopy A D).map ((R M).comparison (S M)))) (by
      intro M N f
      exact (R M).lift_comparison_naturality (S M) (R N) (S N) f)

lemma moduleResolutionHomotopyIso_hom_app
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) (M : ModuleCategory A D) :
    (moduleResolutionHomotopyIso A D R S).hom.app M =
      (moduleToHomotopy A D).map ((R M).comparison (S M)) := rfl

lemma moduleResolutionHomotopyIso_self
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionHomotopyIso A D R R = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simpa only [moduleResolutionHomotopyIso_hom_app, Iso.refl_hom, NatTrans.id_app,
    moduleResolutionHomotopyFunctor] using
    (R M).comparison_self

lemma moduleResolutionHomotopyIso_trans
    (R S T : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionHomotopyIso A D R S ≪≫ moduleResolutionHomotopyIso A D S T =
      moduleResolutionHomotopyIso A D R T := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simpa only [Iso.trans_hom, NatTrans.comp_app, moduleResolutionHomotopyIso_hom_app] using
    (R M).comparison_comp (S M) (T M)

def moduleDerivedResolutionIso
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleDerivedResolutionFunctor A D R ≅ moduleDerivedResolutionFunctor A D S :=
  Localization.liftNatIso (moduleToDerived A D) (moduleQuasiIso A D)
    (moduleResolutionHomotopyFunctor A D R) (moduleResolutionHomotopyFunctor A D S)
    (moduleDerivedResolutionFunctor A D R) (moduleDerivedResolutionFunctor A D S)
    (moduleResolutionHomotopyIso A D R S)

lemma moduleDerivedResolutionIso_hom_app
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) (M : ModuleCategory A D) :
    (moduleDerivedResolutionIso A D R S).hom.app ((moduleToDerived A D).obj M) =
      (moduleDerivedResolutionFunctor_fac A D R).hom.app M ≫
        (moduleResolutionHomotopyIso A D R S).hom.app M ≫
          (moduleDerivedResolutionFunctor_fac A D S).inv.app M :=
  Localization.liftNatTrans_app (moduleToDerived A D) (moduleQuasiIso A D)
    (moduleResolutionHomotopyFunctor A D R) (moduleResolutionHomotopyFunctor A D S)
    (moduleDerivedResolutionFunctor A D R) (moduleDerivedResolutionFunctor A D S)
    (moduleResolutionHomotopyIso A D R S).hom M

lemma moduleDerivedResolutionIso_self
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleDerivedResolutionIso A D R R = Iso.refl _ := by
  apply Iso.ext
  change Localization.liftNatTrans (moduleToDerived A D) (moduleQuasiIso A D)
    (moduleResolutionHomotopyFunctor A D R) (moduleResolutionHomotopyFunctor A D R)
    (moduleDerivedResolutionFunctor A D R) (moduleDerivedResolutionFunctor A D R)
    (moduleResolutionHomotopyIso A D R R).hom = 𝟙 _
  rw [moduleResolutionHomotopyIso_self, Iso.refl_hom, Localization.liftNatTrans_id]

lemma moduleDerivedResolutionIso_trans
    (R S T : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleDerivedResolutionIso A D R S ≪≫ moduleDerivedResolutionIso A D S T =
      moduleDerivedResolutionIso A D R T := by
  apply Iso.ext
  change Localization.liftNatTrans (moduleToDerived A D) (moduleQuasiIso A D)
    (moduleResolutionHomotopyFunctor A D R) (moduleResolutionHomotopyFunctor A D S)
    (moduleDerivedResolutionFunctor A D R) (moduleDerivedResolutionFunctor A D S)
    (moduleResolutionHomotopyIso A D R S).hom ≫
    Localization.liftNatTrans (moduleToDerived A D) (moduleQuasiIso A D)
      (moduleResolutionHomotopyFunctor A D S) (moduleResolutionHomotopyFunctor A D T)
      (moduleDerivedResolutionFunctor A D S) (moduleDerivedResolutionFunctor A D T)
      (moduleResolutionHomotopyIso A D S T).hom =
    Localization.liftNatTrans (moduleToDerived A D) (moduleQuasiIso A D)
      (moduleResolutionHomotopyFunctor A D R) (moduleResolutionHomotopyFunctor A D T)
      (moduleDerivedResolutionFunctor A D R) (moduleDerivedResolutionFunctor A D T)
      (moduleResolutionHomotopyIso A D R T).hom
  rw [Localization.comp_liftNatTrans]
  exact congrArg (fun a => Localization.liftNatTrans (moduleToDerived A D) (moduleQuasiIso A D)
    (moduleResolutionHomotopyFunctor A D R) (moduleResolutionHomotopyFunctor A D T)
    (moduleDerivedResolutionFunctor A D R) (moduleDerivedResolutionFunctor A D T) a)
    (congrArg Iso.hom (moduleResolutionHomotopyIso_trans A D R S T))

end SerrePositivity.DifferentialGraded
end

end ResolutionFunctorChoice
