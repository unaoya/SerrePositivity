module

public import SerrePositivity.DifferentialGraded.Module.ConeConstruction
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison
public import SerrePositivity.DifferentialGraded.Module.Hom.ColimitsAndRightHom
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
public import SerrePositivity.DifferentialGraded.Module.Graded
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations
public import SerrePositivity.DifferentialGraded.Complexes.Cone

/-!
# Module.ConeRotation

## 概要
6 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## ConeHomotopyMap（旧 SerrePositivity/DifferentialGraded/Module/ConeHomotopyMap.lean） -/

/-! # ホモトピーまで可換なsquareによるcone射 -/

@[expose] public section ConeHomotopyMap
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 指定された主Homの要素をそのまま複体のホモトピーへ移す。 -/
def moduleHomotopyComponent {M N : ModuleCategory A D} {f g : M ⟶ N}
    (h : ModuleHomotopy A D f g) (x : D) :
    Homotopy ((moduleEvaluation A D x).map f) ((moduleEvaluation A D x).map g) := by
  let z := (moduleHomπ A D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) N) x).f (-1) h.val
  have hd := congrArg ((moduleHomπ A D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) N) x).f 0) h.property
  change (moduleHomπ A D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) N) x).f 0
      ((moduleHom A D (ForgetEnrichment.to (Complex A) M)
        (ForgetEnrichment.to (Complex A) N)).d (-1) 0 h.val) = _ at hd
  rw [moduleHomElement_d_π, map_sub, ← moduleEvaluation_cochain,
    ← moduleEvaluation_cochain] at hd
  exact (Cochain.equivHomotopy _ _).symm ⟨z, (sub_eq_iff_eq_add).1 hd.symm⟩

lemma moduleHomotopyComponent_cochain {M N : ModuleCategory A D} {f g : M ⟶ N}
    (h : ModuleHomotopy A D f g) (x : D) :
    ((Cochain.equivHomotopy _ _) (moduleHomotopyComponent A D h x)).val =
      (moduleHomπ A D (ForgetEnrichment.to (Complex A) M)
        (ForgetEnrichment.to (Complex A) N) x).f (-1) h.val :=
  congrArg Subtype.val ((Cochain.equivHomotopy _ _).apply_symm_apply _)

/-- squareの両辺を評価した合成で表示する。ホモトピーの成分は変更しない。 -/
def moduleHomotopySquareComponent {M N M' N' : ModuleCategory A D}
    (f : M ⟶ N) (g : M' ⟶ N') (u : M ⟶ M') (v : N ⟶ N')
    (h : ModuleHomotopy A D (f ≫ v) (u ≫ g)) (x : D) :
    Homotopy ((moduleEvaluation A D x).map f ≫ (moduleEvaluation A D x).map v)
      ((moduleEvaluation A D x).map u ≫ (moduleEvaluation A D x).map g) where
  hom := (moduleHomotopyComponent A D h x).hom
  zero := (moduleHomotopyComponent A D h x).zero
  comm p := by
    simpa only [CategoryTheory.Functor.map_comp] using (moduleHomotopyComponent A D h x).comm p

/-- cone射の左入力。hの符号はd h = f≫v − u≫gの規約に従う。 -/
def moduleConeHomotopyInput {M N M' N' : ModuleCategory A D}
    (f : M ⟶ N) (g : M' ⟶ N') (u : M ⟶ M') (v : N ⟶ N')
    (h : ModuleHomotopy A D (f ≫ v) (u ≫ g)) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (moduleCone A D g))).X (-1) :=
  (eHomWhiskerRight (Complex A) u (moduleCone A D g)).f (-1) (moduleConeInlElement A D g) +
    (eHomWhiskerLeft (Complex A) M (moduleConeInr A D g)).f (-1) h.val

lemma moduleConeHomotopyInput_π {M N M' N' : ModuleCategory A D}
    (f : M ⟶ N) (g : M' ⟶ N') (u : M ⟶ M') (v : N ⟶ N')
    (h : ModuleHomotopy A D (f ≫ v) (u ≫ g)) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (moduleCone A D g)) x).f (-1)
        (moduleConeHomotopyInput A D f g u v h) =
      (Cochain.ofHom ((moduleEvaluation A D x).map u)).comp
        (mappingCone.inl ((moduleEvaluation A D x).map g)) (zero_add _) +
      (show Cochain ((moduleEvaluation A D x).obj M) ((moduleEvaluation A D x).obj N') (-1)
        from (moduleHomπ A D (ForgetEnrichment.to (Complex A) M)
          (ForgetEnrichment.to (Complex A) N') x).f (-1) h.val).comp
        (Cochain.ofHom (mappingCone.inr ((moduleEvaluation A D x).map g))) (add_zero _) := by
  rw [moduleConeHomotopyInput, map_add, moduleHomWhiskerRight_apply_π,
    moduleConeInlElement_π, moduleHomWhiskerLeft_apply_π, moduleConeInr_eval]

lemma moduleConeHomotopyInput_d {M N M' N' : ModuleCategory A D}
    (f : M ⟶ N) (g : M' ⟶ N') (u : M ⟶ M') (v : N ⟶ N')
    (h : ModuleHomotopy A D (f ≫ v) (u ≫ g)) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (moduleCone A D g))).d (-1) 0
        (moduleConeHomotopyInput A D f g u v h) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (f ≫ (v ≫ moduleConeInr A D g)))).val := by
  let r := eHomWhiskerRight (Complex A) u (moduleCone A D g)
  let l := eHomWhiskerLeft (Complex A) M (moduleConeInr A D g)
  have hr := congrArg (fun k => k (moduleConeInlElement A D g)) (r.comm (-1) 0)
  have hl := congrArg (fun k => k h.val) (l.comm (-1) 0)
  change (moduleHom A D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) (moduleCone A D g))).d (-1) 0
      (r.f (-1) (moduleConeInlElement A D g)) =
    r.f 0 ((moduleHom A D (ForgetEnrichment.to (Complex A) M')
      (ForgetEnrichment.to (Complex A) (moduleCone A D g))).d (-1) 0
        (moduleConeInlElement A D g)) at hr
  change (moduleHom A D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) (moduleCone A D g))).d (-1) 0 (l.f (-1) h.val) =
    l.f 0 ((moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N')).d (-1) 0 h.val) at hl
  have hh : (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N')).d (-1) 0 h.val =
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (f ≫ v))).val -
          (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (u ≫ g))).val := h.property
  rw [moduleConeInlElement_d] at hr
  rw [hh, map_sub] at hl
  change (moduleHom A D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) (moduleCone A D g))).d (-1) 0
      (r.f (-1) (moduleConeInlElement A D g) + l.f (-1) h.val) = _
  rw [map_add, hr, hl]
  dsimp only [r, l]
  rw [moduleHomCycle_precompose, moduleHomCycle_postcompose, moduleHomCycle_postcompose,
    Category.assoc, Category.assoc]
  abel

/-- ホモトピーまで可換なsquareを全dg自然なcone射に延長する。 -/
def moduleConeMapOfHomotopy {M N M' N' : ModuleCategory A D}
    (f : M ⟶ N) (g : M' ⟶ N') (u : M ⟶ M') (v : N ⟶ N')
    (h : ModuleHomotopy A D (f ≫ v) (u ≫ g)) :
    moduleCone A D f ⟶ moduleCone A D g :=
  moduleConeDescOfBoundary A D f (moduleConeHomotopyInput A D f g u v h)
    (v ≫ moduleConeInr A D g) (moduleConeHomotopyInput_d A D f g u v h)

@[reassoc] lemma moduleConeMapOfHomotopy_inr {M N M' N' : ModuleCategory A D}
    (f : M ⟶ N) (g : M' ⟶ N') (u : M ⟶ M') (v : N ⟶ N')
    (h : ModuleHomotopy A D (f ≫ v) (u ≫ g)) :
    moduleConeInr A D f ≫ moduleConeMapOfHomotopy A D f g u v h = v ≫ moduleConeInr A D g :=
  moduleConeDescOfBoundary_inr A D _ _ _ _


@[simp] lemma moduleConeMapOfHomotopy_eval {M N M' N' : ModuleCategory A D}
    (f : M ⟶ N) (g : M' ⟶ N') (u : M ⟶ M') (v : N ⟶ N')
    (h : ModuleHomotopy A D (f ≫ v) (u ≫ g)) (x : D) :
    (moduleEvaluation A D x).map (moduleConeMapOfHomotopy A D f g u v h) =
      mappingCone.mapOfHomotopy
        (moduleHomotopySquareComponent A D f g u v h x) := by
  unfold moduleConeMapOfHomotopy
  rw [moduleConeDescOfBoundary_eval]
  apply Cochain.ofHom_injective
  rw [mappingCone.ofHom_desc]
  unfold mappingCone.mapOfHomotopy
  rw [mappingCone.ofHom_desc]
  rw [moduleConeHomotopyInput_π, CategoryTheory.Functor.map_comp, moduleConeInr_eval]
  have hc : ((Cochain.equivHomotopy _ _)
      (moduleHomotopySquareComponent A D f g u v h x)).val =
      (moduleHomπ A D (ForgetEnrichment.to (Complex A) M)
        (ForgetEnrichment.to (Complex A) N') x).f (-1) h.val :=
    moduleHomotopyComponent_cochain A D h x
  rw [hc]

@[reassoc] lemma moduleConeMapOfHomotopy_connecting {M N M' N' : ModuleCategory A D}
    (f : M ⟶ N) (g : M' ⟶ N') (u : M ⟶ M') (v : N ⟶ N')
    (h : ModuleHomotopy A D (f ≫ v) (u ≫ g)) :
    moduleConeConnecting A D f ≫ u⟦(1 : ℤ)⟧' =
      moduleConeMapOfHomotopy A D f g u v h ≫ moduleConeConnecting A D g := by
  apply moduleMorphism_ext
  intro x
  simp only [CategoryTheory.Functor.map_comp, moduleConeConnecting_eval,
    moduleConeMapOfHomotopy_eval, moduleShiftFunctor_eq, moduleShiftFunctor_map_eval]
  exact (mappingCone.triangleMapOfHomotopy_comm₃ _).symm

end SerrePositivity.DifferentialGraded
end

end ConeHomotopyMap

/-! ## ConeRotationInputs（旧 SerrePositivity/DifferentialGraded/Module/ConeRotationInputs.lean） -/

/-! # cone三角形の回転比較射の入力と閉性 -/

@[expose] public section ConeRotationInputs
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleConeRotationFirst {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleShiftObj A D 1 M))
      (ForgetEnrichment.to (Complex A) N)).X 1 :=
  -moduleHomLeftShiftElement A D 1 (show (0 : ℤ) + 1 = 1 by omega)
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val

def moduleConeRotationSecond {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleShiftObj A D 1 M))
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).X 0 :=
  -moduleHomLeftShiftElement A D 1 (show (-1 : ℤ) + 1 = 0 by omega)
    (moduleConeInlElement A D f)

lemma moduleConeRotationFirst_π {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) (moduleShiftObj A D 1 M))
      (ForgetEnrichment.to (Complex A) N) x).f 1 (moduleConeRotationFirst A D f) =
      -(Cochain.ofHom ((moduleEvaluation A D x).map f)).leftShift 1 1 (zero_add 1) := by
  unfold moduleConeRotationFirst
  rw [map_neg]
  have h₁ := moduleHomLeftShiftElement_π A D 1
    (show (0 : ℤ) + 1 = 1 by omega)
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val x
  have h₂ := congrArg (fun c => c.leftShift 1 1 (zero_add 1))
    (moduleEvaluation_cochain A D x f).symm
  exact congrArg (fun c => -c) (h₁.trans h₂)

lemma moduleConeRotationSecond_π {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) (moduleShiftObj A D 1 M))
      (ForgetEnrichment.to (Complex A) (moduleCone A D f)) x).f 0
        (moduleConeRotationSecond A D f) =
      -(mappingCone.inl ((moduleEvaluation A D x).map f)).leftShift 1 0 (neg_add_cancel 1) := by
  unfold moduleConeRotationSecond
  rw [map_neg]
  have h₁ := moduleHomLeftShiftElement_π A D 1
    (show (-1 : ℤ) + 1 = 0 by omega) (moduleConeInlElement A D f) x
  have h₂ := congrArg (fun c => c.leftShift 1 0 (neg_add_cancel 1))
    (moduleConeInlElement_π A D f x)
  exact congrArg (fun c => -c) (h₁.trans h₂)

lemma moduleConeRotationFirst_closed {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleShiftObj A D 1 M))
      (ForgetEnrichment.to (Complex A) N)).d 1 2 (moduleConeRotationFirst A D f) = 0 := by
  let z := cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)
  have hd := moduleHomLeftShiftElement_d A D 1
    (M := ForgetEnrichment.to (Complex A) M) (N := ForgetEnrichment.to (Complex A) N)
    (show (0 : ℤ) + 1 = 1 by omega) (show (1 : ℤ) + 1 = 2 by omega) z.val
  have hz : (moduleHom A D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) N)).d 0 1 z.val = 0 := z.property
  rw [hz, moduleHomLeftShiftElement_zero, smul_zero] at hd
  unfold moduleConeRotationFirst
  rw [map_neg]
  exact (congrArg (fun a => -a) hd).trans neg_zero

lemma moduleConeRotationInputs_cycle {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleShiftObj A D 1 M))
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).d 0 1
        (moduleConeRotationSecond A D f) +
      (show (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleShiftObj A D 1 M))
        (ForgetEnrichment.to (Complex A) (moduleCone A D f))).X 1 from
        (eHomWhiskerLeft (Complex A) (moduleShiftObj A D 1 M) (moduleConeInr A D f)).f 1
          (moduleConeRotationFirst A D f)) = 0 := by
  let Z := moduleHom A D (shiftModule 1 (ForgetEnrichment.to (Complex A) M))
    (ForgetEnrichment.to (Complex A) (moduleCone A D f))
  let r : moduleHom A D (shiftModule 1 (ForgetEnrichment.to (Complex A) M))
      (ForgetEnrichment.to (Complex A) N) ⟶ Z :=
    eHomWhiskerLeft (Complex A) (moduleShiftObj A D 1 M) (moduleConeInr A D f)
  let z := (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val
  have hd := moduleHomLeftShiftElement_d A D 1
    (M := ForgetEnrichment.to (Complex A) M)
    (N := ForgetEnrichment.to (Complex A) (moduleCone A D f))
    (show (-1 : ℤ) + 1 = 0 by omega) (show (0 : ℤ) + 1 = 1 by omega)
    (moduleConeInlElement A D f)
  rw [moduleConeInlElement_d] at hd
  have hp := moduleHomLeftShiftElement_postcompose A D 1
    (show (0 : ℤ) + 1 = 1 by omega) z (moduleConeInr A D f)
  have hc := moduleHomCycle_postcompose A D f (moduleConeInr A D f)
  have hp' := (congrArg (moduleHomLeftShiftElement A D 1
    (show (0 : ℤ) + 1 = 1 by omega)) hc).symm.trans hp
  have hs : Z.d 0 1 (moduleHomLeftShiftElement A D 1
      (show (-1 : ℤ) + 1 = 0 by omega) (moduleConeInlElement A D f)) =
      -(r.f 1 (moduleHomLeftShiftElement A D 1
        (show (0 : ℤ) + 1 = 1 by omega) z)) := by
    have hd' := hd.trans (congrArg ((1 : ℤ).negOnePow • ·) hp')
    change Z.d 0 1 (moduleHomLeftShiftElement A D 1
      (show (-1 : ℤ) + 1 = 0 by omega) (moduleConeInlElement A D f)) =
        (1 : ℤ).negOnePow • (r.f 1
          (moduleHomLeftShiftElement A D 1 (show (0 : ℤ) + 1 = 1 by omega) z)) at hd'
    simp only [Int.negOnePow_one, Units.neg_smul, one_smul] at hd'
    exact hd'
  change Z.d 0 1 (-moduleHomLeftShiftElement A D 1
    (show (-1 : ℤ) + 1 = 0 by omega) (moduleConeInlElement A D f)) +
      r.f 1 (-moduleHomLeftShiftElement A D 1 (show (0 : ℤ) + 1 = 1 by omega) z) = 0
  rw [map_neg, map_neg, hs, neg_neg, add_neg_cancel]

/-- M[1]からcone(inr f)への回転比較の順方向。 -/
def moduleConeRotationHom {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleShiftObj A D 1 M ⟶ moduleCone A D (moduleConeInr A D f) :=
  moduleConeLiftOfCycle A D (moduleConeInr A D f)
    (moduleConeRotationFirst A D f) (moduleConeRotationSecond A D f)
    (moduleConeRotationFirst_closed A D f) (moduleConeRotationInputs_cycle A D f)

end SerrePositivity.DifferentialGraded
end

end ConeRotationInputs

/-! ## HomotopyConeTriangle（旧 SerrePositivity/DifferentialGraded/Module/HomotopyConeTriangle.lean） -/

/-! # K(D)の標準cone三角形とホモトピー可換squareの補完 -/

@[expose] public section HomotopyConeTriangle
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

abbrev moduleHomotopyConeTriangle {M N : ModuleCategory A D} (f : M ⟶ N) :
    Triangle (ModuleHomotopyCategory A D) :=
  (moduleToHomotopy A D).mapTriangle.obj (moduleConeTriangle A D f)

/-- 全dg自然なホモトピー可換squareからK(D)の三角形の射を得る。 -/
def moduleHomotopyConeTriangleMap {M N M' N' : ModuleCategory A D}
    (f : M ⟶ N) (g : M' ⟶ N') (u : M ⟶ M') (v : N ⟶ N')
    (h : ModuleHomotopy A D (f ≫ v) (u ≫ g)) :
    moduleHomotopyConeTriangle A D f ⟶ moduleHomotopyConeTriangle A D g where
  hom₁ := (moduleToHomotopy A D).map u
  hom₂ := (moduleToHomotopy A D).map v
  hom₃ := (moduleToHomotopy A D).map (moduleConeMapOfHomotopy A D f g u v h)
  comm₁ := by
    change (moduleToHomotopy A D).map f ≫ (moduleToHomotopy A D).map v =
      (moduleToHomotopy A D).map u ≫ (moduleToHomotopy A D).map g
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact (moduleToHomotopy_map_eq_iff A D _ _).2 ⟨h⟩
  comm₂ := by
    change (moduleToHomotopy A D).map (moduleConeInr A D f) ≫
      (moduleToHomotopy A D).map (moduleConeMapOfHomotopy A D f g u v h) =
        (moduleToHomotopy A D).map v ≫ (moduleToHomotopy A D).map (moduleConeInr A D g)
    rw [← CategoryTheory.Functor.map_comp, moduleConeMapOfHomotopy_inr,
      CategoryTheory.Functor.map_comp]
  comm₃ := by
    dsimp [moduleHomotopyConeTriangle, moduleConeTriangle, Functor.mapTriangle]
    let Q := moduleToHomotopy A D
    have hn := (Q.commShiftIso (1 : ℤ)).hom.naturality u
    change Q.map (u⟦(1 : ℤ)⟧') ≫ (Q.commShiftIso (1 : ℤ)).hom.app M' =
      (Q.commShiftIso (1 : ℤ)).hom.app M ≫ (Q.map u)⟦(1 : ℤ)⟧' at hn
    change (Q.map (moduleConeConnecting A D f) ≫
      (Q.commShiftIso (1 : ℤ)).hom.app M) ≫ (Q.map u)⟦(1 : ℤ)⟧' =
        Q.map (moduleConeMapOfHomotopy A D f g u v h) ≫
          Q.map (moduleConeConnecting A D g) ≫ (Q.commShiftIso (1 : ℤ)).hom.app M'
    rw [Category.assoc, ← hn, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
      moduleConeMapOfHomotopy_connecting, CategoryTheory.Functor.map_comp, Category.assoc]

/-- K(D)で可換なsquareは標準cone三角形の射へ補完できる。 -/
lemma moduleHomotopyConeTriangle_complete {M N M' N' : ModuleCategory A D}
    (f : M ⟶ N) (g : M' ⟶ N')
    (a : (moduleToHomotopy A D).obj M ⟶ (moduleToHomotopy A D).obj M')
    (b : (moduleToHomotopy A D).obj N ⟶ (moduleToHomotopy A D).obj N')
    (comm : (moduleToHomotopy A D).map f ≫ b = a ≫ (moduleToHomotopy A D).map g) :
    ∃ t : moduleHomotopyConeTriangle A D f ⟶ moduleHomotopyConeTriangle A D g,
      t.hom₁ = a ∧ t.hom₂ = b := by
  obtain ⟨a, rfl⟩ := (moduleToHomotopy A D).map_surjective a
  obtain ⟨b, rfl⟩ := (moduleToHomotopy A D).map_surjective b
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp] at comm
  obtain ⟨h⟩ := (moduleToHomotopy_map_eq_iff A D _ _).1 comm
  exact ⟨moduleHomotopyConeTriangleMap A D f g a b h, rfl, rfl⟩

end SerrePositivity.DifferentialGraded
end

end HomotopyConeTriangle

/-! ## ConeContractible（旧 SerrePositivity/DifferentialGraded/Module/ConeContractible.lean） -/

/-! # 恒等射のconeの全dg自然な収縮 -/

@[expose] public section ConeContractible
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleHomCycle_zero (M N : ModuleCategory A D) :
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (0 : M ⟶ N))).val =
      (0 : (moduleHom A D (ForgetEnrichment.to (Complex A) M)
        (ForgetEnrichment.to (Complex A) N)).X 0) := by
  apply moduleHomElement_ext A D
  intro x
  rw [← moduleEvaluation_cochain, CategoryTheory.Functor.map_zero, Cochain.ofHom_zero, map_zero]

def moduleConeInlHomotopy {M N : ModuleCategory A D} (f : M ⟶ N) :
    ModuleHomotopy A D (f ≫ moduleConeInr A D f) 0 :=
  ⟨moduleConeInlElement A D f, by
    change (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).d (-1) 0
        (moduleConeInlElement A D f) = _
    rw [moduleConeInlElement_d, moduleHomCycle_zero, sub_zero]⟩

def moduleConeIdContractingElement (M : ModuleCategory A D) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D (𝟙 M)))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (𝟙 M)))).X (-1) :=
  compose A (x := ForgetEnrichment.to (Complex A) (moduleCone A D (𝟙 M)))
    (y := ForgetEnrichment.to (Complex A) M)
    (z := ForgetEnrichment.to (Complex A) (moduleCone A D (𝟙 M)))
    (moduleConeInlElement A D (𝟙 M)) (moduleConeSndElement A D (𝟙 M)) (by omega)

lemma moduleConeIdContractingElement_π (M : ModuleCategory A D) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) (moduleCone A D (𝟙 M)))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (𝟙 M))) x).f (-1)
        (moduleConeIdContractingElement A D M) =
      (mappingCone.snd ((moduleEvaluation A D x).map (𝟙 M))).comp
        (mappingCone.inl ((moduleEvaluation A D x).map (𝟙 M))) (zero_add (-1)) := by
  rw [moduleConeIdContractingElement, moduleHomCompose_π,
    moduleConeInlElement_π, moduleConeSndElement_π]

lemma moduleConeIdContractingElement_d (M : ModuleCategory A D) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D (𝟙 M)))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (𝟙 M)))).d (-1) 0
        (moduleConeIdContractingElement A D M) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (𝟙 (moduleCone A D (𝟙 M))))).val := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomElement_d_π, moduleConeIdContractingElement_π,
    ← moduleEvaluation_cochain]
  rw [(moduleEvaluation A D x).map_id (moduleCone A D (𝟙 M))]
  change δ (-1) 0
    ((mappingCone.snd ((moduleEvaluation A D x).map (𝟙 M))).comp
      (mappingCone.inl ((moduleEvaluation A D x).map (𝟙 M))) (zero_add (-1))) =
        Cochain.ofHom (𝟙 (mappingCone ((moduleEvaluation A D x).map (𝟙 M))))
  rw [CategoryTheory.Functor.map_id]
  let K := (moduleEvaluation A D x).obj M
  let h := (Cochain.equivHomotopy _ _) (mappingCone.homotopyToZeroOfId K)
  have hc : h.val = (mappingCone.snd (𝟙 K)).comp (mappingCone.inl (𝟙 K)) (zero_add (-1)) := by
    simp [h, mappingCone.homotopyToZeroOfId, mappingCone.descHomotopy, mappingCone.descCochain]
  have hd := h.property
  rw [hc, Cochain.ofHom_zero, add_zero] at hd
  exact hd.symm

def moduleConeIdHomotopy (M : ModuleCategory A D) :
    ModuleHomotopy A D (𝟙 (moduleCone A D (𝟙 M))) 0 :=
  ⟨moduleConeIdContractingElement A D M, by
    change (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D (𝟙 M)))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (𝟙 M)))).d (-1) 0
        (moduleConeIdContractingElement A D M) = _
    rw [moduleConeIdContractingElement_d, moduleHomCycle_zero, sub_zero]⟩


lemma moduleConeId_isZero (M : ModuleCategory A D) :
    IsZero ((moduleToHomotopy A D).obj (moduleCone A D (𝟙 M))) := by
  apply (IsZero.iff_id_eq_zero _).2
  have h := (moduleToHomotopy_map_eq_iff A D
    (𝟙 (moduleCone A D (𝟙 M))) 0).2 ⟨moduleConeIdHomotopy A D M⟩
  simpa only [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero] using h

instance moduleHomotopyHasZeroObject : HasZeroObject (ModuleHomotopyCategory A D) :=
  ((moduleToHomotopy A D).map_isZero (isZero_zero (ModuleCategory A D))).hasZeroObject

end SerrePositivity.DifferentialGraded
end

end ConeContractible

/-! ## ConeRotation（旧 SerrePositivity/DifferentialGraded/Module/ConeRotation.lean） -/

/-! # coneの回転比較射と各評価での既存比較との一致 -/

@[expose] public section ConeRotation
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

@[simp] lemma moduleConeRotationHom_eval {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).map (moduleConeRotationHom A D f) =
      complexConeRotationHom ((moduleEvaluation A D x).map f)
        ((moduleEvaluation A D x).map (moduleConeInr A D f)) (moduleConeInr_eval A D f x) := by
  unfold moduleConeRotationHom
  rw [moduleConeLiftOfCycle_eval]
  apply Cochain.ofHom_injective
  rw [mappingCone.ofHom_lift, complexConeRotationHom_cochain]
  change mappingCone.liftCochain ((moduleEvaluation A D x).map (moduleConeInr A D f))
    ((moduleHomπ A D (ForgetEnrichment.to (Complex A) (moduleShiftObj A D 1 M))
      (ForgetEnrichment.to (Complex A) N) x).f 1 (moduleConeRotationFirst A D f))
    ((moduleHomπ A D (ForgetEnrichment.to (Complex A) (moduleShiftObj A D 1 M))
      (ForgetEnrichment.to (Complex A) (moduleCone A D f)) x).f 0
        (moduleConeRotationSecond A D f)) (zero_add 1) = _
  rw [moduleConeRotationFirst_π, moduleConeRotationSecond_π]

@[reassoc] lemma moduleConeInr_connecting_zero {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleConeInr A D f ≫ moduleConeConnecting A D f = 0 := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, moduleConeInr_eval, moduleConeConnecting_eval,
    CategoryTheory.Functor.map_zero]
  exact mappingCone.inr_triangleδ _

lemma moduleConeRotationInv_condition {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) (moduleShiftObj A D 1 M))).d (-1) 0 0 =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (moduleConeInr A D f ≫ moduleConeConnecting A D f))).val := by
  rw [map_zero, moduleConeInr_connecting_zero, moduleHomCycle_zero]

def moduleConeRotationInv {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleCone A D (moduleConeInr A D f) ⟶ moduleShiftObj A D 1 M :=
  moduleConeDescOfBoundary A D (moduleConeInr A D f) 0
    (moduleConeConnecting A D f) (moduleConeRotationInv_condition A D f)

@[simp] lemma moduleConeRotationInv_eval {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).map (moduleConeRotationInv A D f) =
      complexConeRotationInv ((moduleEvaluation A D x).map f)
        ((moduleEvaluation A D x).map (moduleConeInr A D f)) (moduleConeInr_eval A D f x) := by
  unfold moduleConeRotationInv
  rw [moduleConeDescOfBoundary_eval]
  apply Cochain.ofHom_injective
  rw [mappingCone.ofHom_desc, complexConeRotationInv_cochain, map_zero,
    moduleConeConnecting_eval]

lemma moduleConeRotation_hom_inv {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleConeRotationHom A D f ≫ moduleConeRotationInv A D f = 𝟙 _ := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, moduleConeRotationHom_eval,
    moduleConeRotationInv_eval, CategoryTheory.Functor.map_id]
  exact complexConeRotation_hom_inv _ _ _

end SerrePositivity.DifferentialGraded
end

end ConeRotation

/-! ## ConeRotationHomotopy（旧 SerrePositivity/DifferentialGraded/Module/ConeRotationHomotopy.lean） -/

/-! # 回転比較の全dg自然な収縮とK(D)の同型 -/

@[expose] public section ConeRotationHomotopy
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleConeRotationConnectingElement {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeInr A D f)))).X (-1) :=
  -compose A (x := ForgetEnrichment.to (Complex A) (moduleCone A D f))
    (y := ForgetEnrichment.to (Complex A) N)
    (z := ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeInr A D f)))
    (moduleConeInlElement A D (moduleConeInr A D f)) (moduleConeSndElement A D f) (by omega)

def moduleConeRotationContractingElement {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeInr A D f)))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeInr A D f)))).X (-1) :=
  compose A (x := ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeInr A D f)))
    (y := ForgetEnrichment.to (Complex A) (moduleCone A D f))
    (z := ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeInr A D f)))
    (moduleConeRotationConnectingElement A D f)
    (moduleConeSndElement A D (moduleConeInr A D f)) (by omega)

lemma moduleConeRotationConnectingElement_π {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeInr A D f))) x).f (-1)
        (moduleConeRotationConnectingElement A D f) =
      -(mappingCone.snd ((moduleEvaluation A D x).map f)).comp
        (mappingCone.inl ((moduleEvaluation A D x).map (moduleConeInr A D f))) (zero_add (-1)) := by
  rw [moduleConeRotationConnectingElement, map_neg, moduleHomCompose_π,
    moduleConeSndElement_π, moduleConeInlElement_π]

lemma moduleConeRotationContractingElement_π {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeInr A D f)))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeInr A D f))) x).f (-1)
        (moduleConeRotationContractingElement A D f) =
      -(mappingCone.snd ((moduleEvaluation A D x).map (moduleConeInr A D f))).comp
        ((mappingCone.snd ((moduleEvaluation A D x).map f)).comp
          (mappingCone.inl ((moduleEvaluation A D x).map (moduleConeInr A D f))) (zero_add (-1)))
        (zero_add (-1)) := by
  rw [moduleConeRotationContractingElement, moduleHomCompose_π,
    moduleConeSndElement_π, moduleConeRotationConnectingElement_π, Cochain.comp_neg]

lemma moduleConeRotationContractingElement_d {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeInr A D f)))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeInr A D f)))).d (-1) 0
        (moduleConeRotationContractingElement A D f) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (moduleConeRotationInv A D f ≫ moduleConeRotationHom A D f))).val -
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (𝟙 (moduleCone A D (moduleConeInr A D f))))).val := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomElement_d_π, moduleConeRotationContractingElement_π, map_sub,
    ← moduleEvaluation_cochain, ← moduleEvaluation_cochain, CategoryTheory.Functor.map_comp,
    moduleConeRotationInv_eval, moduleConeRotationHom_eval, CategoryTheory.Functor.map_id]
  exact complexConeRotation_inv_hom_boundary _ _ _

def moduleConeRotationInvHomHomotopy {M N : ModuleCategory A D} (f : M ⟶ N) :
    ModuleHomotopy A D (moduleConeRotationInv A D f ≫ moduleConeRotationHom A D f) (𝟙 _) :=
  ⟨moduleConeRotationContractingElement A D f, moduleConeRotationContractingElement_d A D f⟩

lemma moduleConeRotationConnectingElement_d {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeInr A D f)))).d (-1) 0
        (moduleConeRotationConnectingElement A D f) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (moduleConeConnecting A D f ≫ moduleConeRotationHom A D f))).val -
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (moduleConeInr A D (moduleConeInr A D f)))).val := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomElement_d_π, moduleConeRotationConnectingElement_π, map_sub,
    ← moduleEvaluation_cochain, ← moduleEvaluation_cochain, CategoryTheory.Functor.map_comp,
    moduleConeConnecting_eval, moduleConeRotationHom_eval,
    moduleConeInr_eval A D (moduleConeInr A D f) x]
  exact complexConeRotation_connecting_boundary _ _ _

def moduleConeRotationConnectingHomotopy {M N : ModuleCategory A D} (f : M ⟶ N) :
    ModuleHomotopy A D (moduleConeConnecting A D f ≫ moduleConeRotationHom A D f)
      (moduleConeInr A D (moduleConeInr A D f)) :=
  ⟨moduleConeRotationConnectingElement A D f, moduleConeRotationConnectingElement_d A D f⟩

lemma moduleConeRotation_connecting {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleConeRotationHom A D f ≫ moduleConeConnecting A D (moduleConeInr A D f) =
      -f⟦(1 : ℤ)⟧' := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, moduleConeRotationHom_eval,
    moduleConeConnecting_eval, CategoryTheory.Functor.map_neg]
  have hs : (moduleEvaluation A D x).map (f⟦(1 : ℤ)⟧') =
      ((moduleEvaluation A D x).map f)⟦(1 : ℤ)⟧' :=
    moduleShiftFunctor_map_eval A D 1 f x
  rw [hs]
  exact complexConeRotation_connecting _ _ _

/-- 回転比較の第三対象の同型。 -/
def moduleConeRotationHomotopyIso {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleToHomotopy A D).obj (moduleShiftObj A D 1 M) ≅
      (moduleToHomotopy A D).obj (moduleCone A D (moduleConeInr A D f)) where
  hom := (moduleToHomotopy A D).map (moduleConeRotationHom A D f)
  inv := (moduleToHomotopy A D).map (moduleConeRotationInv A D f)
  hom_inv_id := by
    rw [← CategoryTheory.Functor.map_comp, moduleConeRotation_hom_inv,
      CategoryTheory.Functor.map_id]
  inv_hom_id := by
    rw [← CategoryTheory.Functor.map_comp]
    exact ((moduleToHomotopy_map_eq_iff A D _ _).2
      ⟨moduleConeRotationInvHomHomotopy A D f⟩).trans ((moduleToHomotopy A D).map_id _)


/-- 商関手のshift比較を含めた、回転三角形の第三対象の同型。 -/
def moduleConeRotationShiftIso {M N : ModuleCategory A D} (f : M ⟶ N) :
    ((moduleToHomotopy A D).obj M)⟦(1 : ℤ)⟧ ≅
      (moduleToHomotopy A D).obj (moduleCone A D (moduleConeInr A D f)) :=
  ((moduleToHomotopy A D).commShiftIso (1 : ℤ)).symm.app M ≪≫
    moduleConeRotationHomotopyIso A D f

end SerrePositivity.DifferentialGraded
end

end ConeRotationHomotopy
