module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.DifferentialGraded.Perfect.Ring.FiniteProjectiveComparison
public import SerrePositivity.DifferentialGraded.Perfect.Compact.Enhancement
public import Mathlib.CategoryTheory.Functor.OfSequence
public import SerrePositivity.DifferentialGraded.Perfect.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import SerrePositivity.DifferentialGraded.Module.TensorFree
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution

public import SerrePositivity.DifferentialGraded.Complexes.Perturbation
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementOperations
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
public import SerrePositivity.DifferentialGraded.Category.Basic

/-!
# Perfect.Compact.FiniteGeneration

## 概要
compact ⇒ Perf の有限 cell 因子分解と有限射影代表・冪等完備性をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## RingTriangleFiniteModel（旧 SerrePositivity/DifferentialGraded/Perfect/RingTriangleFiniteModel.lean） -/

/-! # 逆回転三角形から有限射影代表を戻す

single→X→Kの両端が有限射影で表されるとき、実際のchain mapのconeでXを表す。
-/

@[expose] public section RingTriangleFiniteModel
universe u w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex Pretriangulated
variable (A : Type u) [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]

lemma ringDerivedTriangle_middle_finiteRange
    (T : Triangle (DerivedCategory (ModuleCat.{u} A))) (hT : T ∈ distTriang _)
    (F : ModuleCat.{u} A) [Module.Finite A F] [Module.Projective A F]
    (K : Complex A) (hK : strictlyPerfectComplex A K) (a b : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE (b - 1)] (hab : a ≤ b)
    (eF : DerivedCategory.Q.obj ((single (ModuleCat.{u} A) (.up ℤ) b).obj F) ≅ T.obj₁)
    (eK : DerivedCategory.Q.obj K ≅ T.obj₃) :
    ∃ L : Complex A, strictlyPerfectComplex A L ∧ L.IsStrictlyGE a ∧ L.IsStrictlyLE b ∧
      Nonempty (DerivedCategory.Q.obj L ≅ T.obj₂) := by
  let S := (single (ModuleCat.{u} A) (.up ℤ) b).obj F
  let K' := K⟦(-1 : ℤ)⟧
  have hK' : strictlyPerfectComplex A K' := strictlyPerfectComplex_shift hK (-1)
  have : K'.IsStrictlyGE (a + 1) := K.isStrictlyGE_shift a (-1) (a + 1) (by omega)
  have : K'.IsStrictlyLE b := K.isStrictlyLE_shift (b - 1) (-1) b (by omega)
  let Q := DerivedCategory.Q (C := ModuleCat.{u} A)
  let e₁ : Q.obj K' ≅ T.invRotate.obj₁ := (Q.commShiftIso (-1 : ℤ)).app K ≪≫
    (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-1 : ℤ)).mapIso eK
  let h := e₁.hom ≫ T.invRotate.mor₁ ≫ eF.inv
  obtain ⟨f, hf⟩ := ringComplexDerived_map_surjective A K' hK' S h
  let C := Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)
  let e : C ≅ T.invRotate := isoTriangleOfIso₁₂ C T.invRotate
    (DerivedCategory.mappingCone_triangle_distinguished f) (inv_rot_of_distTriang T hT)
    e₁ eF (by
      change Q.map f ≫ eF.hom = e₁.hom ≫ T.invRotate.mor₁
      rw [hf]
      simp only [h, Category.assoc, Iso.inv_hom_id, Category.comp_id])
  have hL : strictlyPerfectComplex A (CochainComplex.mappingCone f) :=
    strictlyPerfectComplex_mappingCone A f hK' (strictlyPerfectComplex_single A F b)
  have hge : (CochainComplex.mappingCone f).IsStrictlyGE a :=
    CochainComplex.isStrictlyGE_mappingCone f (a + 1) b a (by omega) hab
  have hle : (CochainComplex.mappingCone f).IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨K'.isZero_of_isStrictlyLE b (i + 1) (by omega),
      CochainComplex.isZero_of_isStrictlyLE S b i hi⟩
  exact ⟨_, hL, hge, hle, ⟨Triangle.π₃.mapIso e⟩⟩

end SerrePositivity.DifferentialGraded
end

end RingTriangleFiniteModel

/-! ## RingRetractFiniteRepresentative（旧 SerrePositivity/DifferentialGraded/Perfect/RingRetractFiniteRepresentative.lean） -/

/-! # 有限射影複体の導来retractの有限射影代表

次数幅の帰納法。上端被覆で短い幅へ帰着し、逆回転三角形のconeで元の対象へ戻す。
-/

@[expose] public section RingRetractFiniteRepresentative
universe u w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex Pretriangulated
variable (A : Type u) [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]

lemma ringDerivedRetract_finiteRange (width : ℕ) (a : ℤ)
    (P : Complex A) (hP : strictlyPerfectComplex A P)
    (hge : P.IsStrictlyGE a) (hle : P.IsStrictlyLE (a + (width : ℤ)))
    {X : DerivedCategory (ModuleCat.{u} A)} (r : Retract X (DerivedCategory.Q.obj P)) :
    ∃ K : Complex A, strictlyPerfectComplex A K ∧ K.IsStrictlyGE a ∧
      K.IsStrictlyLE (a + (width : ℤ)) ∧ Nonempty (DerivedCategory.Q.obj K ≅ X) := by
  induction width generalizing a P X with
  | zero =>
    let := hge
    have : P.IsStrictlyLE a := by simpa only [Nat.cast_zero, add_zero] using hle
    simpa only [Nat.cast_zero, add_zero] using ringDerivedRetract_pure_finiteRange A P hP a r
  | succ width ih =>
    let b := a + (width : ℤ) + 1
    have hbound : a + (width.succ : ℤ) = b := by dsimp only [b]; omega
    let := hge
    have : P.IsStrictlyLE b := by simpa only [hbound] using hle
    have hab : a < b := by dsimp only [b]; omega
    obtain ⟨F, hf, hp, T, hT, h₁, h₂, P', hP', hge', hle', ⟨r'⟩⟩ :=
      ringDerivedRetract_reduce_range A P hP a b r hab
    have hb : b - 1 = a + (width : ℤ) := by dsimp only [b]; omega
    have hleW : P'.IsStrictlyLE (a + (width : ℤ)) := by simpa only [hb] using hle'
    obtain ⟨K, hK, hgeK, hleK, ⟨eK⟩⟩ := ih a P' hP' hge' hleW r'
    let := hf
    let := hp
    let := hgeK
    have : K.IsStrictlyLE (b - 1) := by simpa only [hb] using hleK
    obtain ⟨L, hL, hgeL, hleL, ⟨eL⟩⟩ := ringDerivedTriangle_middle_finiteRange A T hT F K hK
      a b hab.le (eqToIso h₁).symm eK
    refine ⟨L, hL, hgeL, ?_, ⟨eL ≪≫ eqToIso h₂⟩⟩
    simpa only [hbound] using hleL

lemma ringDerivedRetract_finiteProjective (P : Complex A) (hP : strictlyPerfectComplex A P)
    {X : DerivedCategory (ModuleCat.{u} A)} (r : Retract X (DerivedCategory.Q.obj P)) :
    ∃ K : Complex A, strictlyPerfectComplex A K ∧ Nonempty (DerivedCategory.Q.obj K ≅ X) := by
  obtain ⟨a, b, ha, hb⟩ := hP.1
  let := ha
  let := hb
  let width := (b - a).toNat
  have hle : P.IsStrictlyLE (a + (width : ℤ)) :=
    P.isStrictlyLE_of_le b _ (by dsimp only [width]; omega)
  obtain ⟨K, hK, _, _, e⟩ := ringDerivedRetract_finiteRange A width a P hP ha hle r
  exact ⟨K, hK, e⟩

end SerrePositivity.DifferentialGraded
end

end RingRetractFiniteRepresentative

/-! ## RingPerfectRepresentatives（旧 SerrePositivity/DifferentialGraded/Perfect/RingPerfectRepresentatives.lean） -/

/-! # 一対象Aの主Perfの全対象の有界有限射影代表 -/

@[expose] public section RingPerfectRepresentatives
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A]
local instance : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

def ringModule_complexDerivedIso (M : ModuleCategory A PUnit.{1}) :
    (moduleToDerived A PUnit.{1}).obj ((complexToRingModule A).obj
        ((moduleEvaluation A PUnit.{1} PUnit.unit).obj M)) ≅
      (moduleToDerived A PUnit.{1}).obj M :=
  eqToIso (congrArg
    (fun N => (moduleToDerived A PUnit.{1}).obj (ForgetEnrichment.of (Complex A) N))
    (ringModule_recover A (ForgetEnrichment.to (Complex A) M)))

lemma ringModuleDerivedRetract_finiteProjective (P : Complex A)
    (hP : strictlyPerfectComplex A P) {X : DerivedModuleCategory A PUnit.{1}}
    (r : Retract X ((moduleToDerived A PUnit.{1}).obj ((complexToRingModule A).obj P))) :
    ∃ K : Complex A, strictlyPerfectComplex A K ∧
      Nonempty ((moduleToDerived A PUnit.{1}).obj ((complexToRingModule A).obj K) ≅ X) := by
  let E := ringDerivedEquivalence A
  let eP : E.functor.obj ((moduleToDerived A PUnit.{1}).obj ((complexToRingModule A).obj P)) ≅
      DerivedCategory.Q.obj P := (complexToRingModuleDerivedEvaluationIso A).app P
  obtain ⟨K, hK, ⟨eK⟩⟩ := ringDerivedRetract_finiteProjective A P hP
    ((r.map E.functor).trans (Retract.ofIso eP))
  let e : E.functor.obj ((moduleToDerived A PUnit.{1}).obj ((complexToRingModule A).obj K)) ≅
      E.functor.obj X := (complexToRingModuleDerivedEvaluationIso A).app K ≪≫ eK
  exact ⟨K, hK, ⟨(Functor.FullyFaithful.ofFullyFaithful E.functor).preimageIso e⟩⟩

lemma modulePerfect_ring_has_strictlyPerfectRepresentative
    {X : DerivedModuleCategory A PUnit.{1}} (hX : modulePerfect A PUnit.{1} X) :
    ∃ K : Complex A, strictlyPerfectComplex A K ∧
      Nonempty ((moduleToDerived A PUnit.{1}).obj ((complexToRingModule A).obj K) ≅ X) := by
  obtain ⟨M, hM, ⟨r⟩⟩ := (modulePerfect_iff A PUnit.{1} X).1 hX
  let P := (moduleEvaluation A PUnit.{1} PUnit.unit).obj M
  have hP : strictlyPerfectComplex A P := moduleFiniteCell_ringEvaluation_strictlyPerfect A hM
  exact ringModuleDerivedRetract_finiteProjective A P hP
    (r.trans (Retract.ofIso (ringModule_complexDerivedIso A M).symm))

end SerrePositivity.DifferentialGraded
end

end RingPerfectRepresentatives

/-! ## CompactConverseTelescope（旧 SerrePositivity/DifferentialGraded/Perfect/CompactConverseTelescope.lean） -/

/-! # compact ⇒ Perf に向けた可算 telescope の有限段階因子分解

ここでは任意の列に対する三角圏内の telescope を扱う。
semifree filtration の余極限との比較、有限 cell への因子分解は別の課題である。
-/

@[expose] public section CompactConverseTelescope
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Preadditive Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleCompact_hom_ext_zero {J : Type u} {X : DerivedModuleCategory A D}
    (hX : moduleCompact A D X) (F : J → DerivedModuleCategory A D)
    (f : X ⟶ ∐ F) (hf : ∀ n, f ≫ moduleDerivedCoproductProjection A D F n = 0) :
    f = 0 := by
  classical
  obtain ⟨t, g, hg⟩ := hX J F f
  have hgi (i : J) (hi : i ∈ t) : g i = 0 := by
    have h := congrArg (fun k => k ≫ moduleDerivedCoproductProjection A D F i) hg
    rw [sum_comp, hf] at h
    rw [Finset.sum_eq_single i] at h
    · simpa only [Category.assoc, moduleDerivedCoproductProjection_self,
        Category.comp_id] using h
    · intro j _ hji
      rw [Category.assoc, moduleDerivedCoproductProjection_ne A D F j i hji, comp_zero]
    · exact fun h => (h hi).elim
  rw [← hg]
  exact Finset.sum_eq_zero (fun i hi => by rw [hgi i hi, zero_comp])

variable (F : ℕ → DerivedModuleCategory A D) (d : ∀ n, F n ⟶ F (n + 1))

/-- 可算添字を u に持ち上げ、既存の compact API と同じ余積を使う。 -/
abbrev moduleTelescopeFamily (n : ULift.{u} ℕ) := F n.down

def moduleTelescopeShift : (∐ moduleTelescopeFamily A D F) ⟶ ∐ moduleTelescopeFamily A D F :=
  Sigma.desc (fun n => d n.down ≫ Sigma.ι (moduleTelescopeFamily A D F) ⟨n.down + 1⟩)

def moduleTelescopeMap : (∐ moduleTelescopeFamily A D F) ⟶ ∐ moduleTelescopeFamily A D F :=
  𝟙 _ - moduleTelescopeShift A D F d

lemma moduleTelescopeShift_projection_zero :
    moduleTelescopeShift A D F d ≫
      moduleDerivedCoproductProjection A D (moduleTelescopeFamily A D F) ⟨0⟩ = 0 := by
  apply Sigma.hom_ext
  intro n
  simp [moduleTelescopeShift, Category.assoc, moduleDerivedCoproductProjection]

lemma moduleTelescopeShift_projection_succ (n : ℕ) :
    moduleTelescopeShift A D F d ≫
      moduleDerivedCoproductProjection A D (moduleTelescopeFamily A D F) ⟨n + 1⟩ =
      moduleDerivedCoproductProjection A D (moduleTelescopeFamily A D F) ⟨n⟩ ≫ d n := by
  apply Sigma.hom_ext
  intro ⟨i⟩
  by_cases h : i = n
  · subst i
    simp only [moduleTelescopeShift, Sigma.ι_comp_desc_assoc, Category.assoc]
    rw [moduleDerivedCoproductProjection_self, Category.comp_id, ← Category.assoc,
      moduleDerivedCoproductProjection_self, Category.id_comp]
  · simp only [moduleTelescopeShift, Sigma.ι_comp_desc_assoc, Category.assoc]
    rw [moduleDerivedCoproductProjection_ne A D (moduleTelescopeFamily A D F)
      ⟨i + 1⟩ ⟨n + 1⟩ (by simp; omega), comp_zero, ← Category.assoc,
      moduleDerivedCoproductProjection_ne A D (moduleTelescopeFamily A D F) ⟨i⟩ ⟨n⟩
        (by simpa using h), zero_comp]

/-- compact な始域の Hom 上では 1-shift は単射。 -/
lemma moduleCompact_telescopeMap_zero {X : DerivedModuleCategory A D}
    (hX : moduleCompact A D X) (f : X ⟶ ∐ moduleTelescopeFamily A D F)
    (hf : f ≫ moduleTelescopeMap A D F d = 0) : f = 0 := by
  have he : f = f ≫ moduleTelescopeShift A D F d := by
    simpa only [moduleTelescopeMap, comp_sub, Category.comp_id, sub_eq_zero] using hf
  apply moduleCompact_hom_ext_zero A D hX (moduleTelescopeFamily A D F) f
  intro ⟨n⟩
  induction n with
  | zero => rw [he, Category.assoc, moduleTelescopeShift_projection_zero, comp_zero]
  | succ n ih =>
    calc
      _ = f ≫ moduleTelescopeShift A D F d ≫
          moduleDerivedCoproductProjection A D (moduleTelescopeFamily A D F) ⟨n + 1⟩ := by
            rw [← Category.assoc, ← he]
      _ = 0 := by rw [moduleTelescopeShift_projection_succ, ← Category.assoc, ih, zero_comp]

lemma moduleCompact_shiftedTelescopeMap_zero {X : DerivedModuleCategory A D}
    (hX : moduleCompact A D X)
    (f : X ⟶ (∐ moduleTelescopeFamily A D F)⟦(1 : ℤ)⟧)
    (hf : f ≫ (moduleTelescopeMap A D F d)⟦(1 : ℤ)⟧' = 0) : f = 0 := by
  let E := shiftEquiv' (DerivedModuleCategory A D) (-1 : ℤ) 1 (by omega)
  have : E.functor.Additive :=
    inferInstanceAs (shiftFunctor (DerivedModuleCategory A D) (-1 : ℤ)).Additive
  let e := E.toAdjunction.homAddEquiv X (∐ moduleTelescopeFamily A D F)
  let a := e.symm f
  have ha : a ≫ moduleTelescopeMap A D F d = 0 := by
    apply e.injective
    rw [map_zero]
    change E.toAdjunction.homEquiv _ _ (a ≫ _) = 0
    rw [E.toAdjunction.homEquiv_naturality_right]
    change e a ≫ _ = 0
    rw [show e a = f from e.apply_symm_apply f]
    exact hf
  have ha0 := moduleCompact_telescopeMap_zero A D F d (moduleCompact_shift A D hX (-1)) a ha
  calc
    f = e a := (e.apply_symm_apply f).symm
    _ = 0 := by rw [ha0, map_zero]

/-- 任意の telescope 三角形への射は、余積の有限個の成分を経由する。 -/
lemma moduleCompact_telescope_finite_lift {X Y : DerivedModuleCategory A D}
    (hX : moduleCompact A D X) (c : (∐ moduleTelescopeFamily A D F) ⟶ Y)
    (b : Y ⟶ (∐ moduleTelescopeFamily A D F)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (moduleTelescopeMap A D F d) c b ∈
      distTriang (DerivedModuleCategory A D)) (f : X ⟶ Y) :
    ∃ (t : Finset (ULift.{u} ℕ)) (g : ∀ n, X ⟶ F n.down),
      f = ∑ n ∈ t, g n ≫ Sigma.ι (moduleTelescopeFamily A D F) n ≫ c := by
  have hz : b ≫ (moduleTelescopeMap A D F d)⟦(1 : ℤ)⟧' = 0 :=
    comp_distTriang_mor_zero₃₁ _ hT
  have hfb : f ≫ b = 0 := moduleCompact_shiftedTelescopeMap_zero A D F d hX (f ≫ b)
    (by rw [Category.assoc, hz, comp_zero])
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₃ _ hT f hfb
  change f = g ≫ c at hg
  obtain ⟨t, a, ha⟩ := hX (ULift.{u} ℕ) (moduleTelescopeFamily A D F) g
  refine ⟨t, a, ?_⟩
  rw [hg, ← ha, sum_comp]
  simp only [Category.assoc]

/-- compact な対象から telescope への射は一つの有限段階を経由する。 -/
lemma moduleCompact_telescope_factor {X Y : DerivedModuleCategory A D}
    (hX : moduleCompact A D X) (c : (∐ moduleTelescopeFamily A D F) ⟶ Y)
    (b : Y ⟶ (∐ moduleTelescopeFamily A D F)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (moduleTelescopeMap A D F d) c b ∈
      distTriang (DerivedModuleCategory A D)) (f : X ⟶ Y) :
    ∃ (n : ℕ) (g : X ⟶ F n),
      f = g ≫ Sigma.ι (moduleTelescopeFamily A D F) ⟨n⟩ ≫ c := by
  classical
  let j (n : ℕ) := Sigma.ι (moduleTelescopeFamily A D F) ⟨n⟩ ≫ c
  have hj (n : ℕ) : d n ≫ j (n + 1) = j n := by
    have h := congrArg (fun k => Sigma.ι (moduleTelescopeFamily A D F) ⟨n⟩ ≫ k)
      (comp_distTriang_mor_zero₁₂ _ hT)
    change _ ≫ (moduleTelescopeMap A D F d ≫ c) = _ at h
    have he : j n = d n ≫ j (n + 1) := by
      simpa only [moduleTelescopeMap, moduleTelescopeShift, comp_sub, sub_comp,
        Category.comp_id, Category.assoc, Category.id_comp, Sigma.ι_comp_desc_assoc,
        comp_zero, sub_eq_zero, j] using h
    exact he.symm
  let α : Functor.ofSequence d ⟶ (Functor.const ℕ).obj Y :=
    NatTrans.ofSequence j (by intro n; simpa using hj n)
  obtain ⟨t, a, ha⟩ := moduleCompact_telescope_finite_lift A D F d hX c b hT f
  let N := t.sup (fun n => n.down)
  refine ⟨N, ∑ n ∈ t, (if hn : n.down ≤ N then
    a n ≫ (Functor.ofSequence d).map (homOfLE hn) else 0), ?_⟩
  rw [sum_comp, ha]
  apply Finset.sum_congr rfl
  intro n hn
  have hnN : n.down ≤ N := Finset.le_sup (f := fun n => n.down) hn
  rw [dite_eq_left hnN, Category.assoc]
  have h := α.naturality (homOfLE hnN)
  change (Functor.ofSequence d).map _ ≫ j N = j n.down ≫ 𝟙 Y at h
  rw [Category.comp_id] at h
  exact (congrArg (fun k => a n ≫ k) h).symm

/-- compact な telescope 対象は、有限高さの一段階の retract である。 -/
lemma moduleCompact_telescope_retract {X : DerivedModuleCategory A D}
    (hX : moduleCompact A D X) (c : (∐ moduleTelescopeFamily A D F) ⟶ X)
    (b : X ⟶ (∐ moduleTelescopeFamily A D F)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (moduleTelescopeMap A D F d) c b ∈
      distTriang (DerivedModuleCategory A D)) :
    ∃ n : ℕ, Nonempty (Retract X (F n)) := by
  obtain ⟨n, g, hg⟩ := moduleCompact_telescope_factor A D F d hX c b hT (𝟙 X)
  exact ⟨n, ⟨{
    i := g
    r := Sigma.ι (moduleTelescopeFamily A D F) ⟨n⟩ ≫ c
    retract := hg.symm }⟩⟩

end SerrePositivity.DifferentialGraded
end

end CompactConverseTelescope

/-! ## CompactConverseFactor（旧 SerrePositivity/DifferentialGraded/Perfect/CompactConverseFactor.lean） -/

/-! # 有限 cell を経由する射と compact 性

compact ⇒ Perf の有限因子分解の基底段階。対象を有限 cell と仮定する条件と、
任意の compact な始域からの射が有限 cell を経由する条件とを区別する。
-/

@[expose] public section CompactConverseFactor
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Preadditive Pretriangulated
open scoped ZeroObject
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 射が指定有限 cell の導来像を経由する。 -/
def ModuleFiniteCellFactor (S : Set D) {X Y : DerivedModuleCategory A D} (f : X ⟶ Y) : Prop :=
  ∃ (P : DerivedModuleCategory A D), derivedFiniteCellOver A D S P ∧
    ∃ (a : X ⟶ P) (b : P ⟶ Y), a ≫ b = f

lemma moduleFiniteCellFactor_zero (S : Set D) (X Y : DerivedModuleCategory A D) :
    ModuleFiniteCellFactor A D S (0 : X ⟶ Y) :=
  ⟨0, (derivedFiniteCellOver A D S).prop_zero, 0, 0, zero_comp⟩

lemma ModuleFiniteCellFactor.add {S : Set D} {X Y : DerivedModuleCategory A D}
    {f g : X ⟶ Y} (hf : ModuleFiniteCellFactor A D S f)
    (hg : ModuleFiniteCellFactor A D S g) : ModuleFiniteCellFactor A D S (f + g) := by
  obtain ⟨P, hP, a, b, hab⟩ := hf
  obtain ⟨Q, hQ, c, d, hcd⟩ := hg
  have hPQ : derivedFiniteCellOver A D S (P ⊞ Q) :=
    (derivedFiniteCellOver A D S).prop_of_iso (biprod.isoProd P Q).symm
      ((derivedFiniteCellOver A D S).prop_prod P Q hP hQ)
  exact ⟨P ⊞ Q, hPQ, biprod.lift a c, biprod.desc b d,
    by rw [biprod.lift_desc, hab, hcd]⟩

lemma ModuleFiniteCellFactor.postcompose {S : Set D} {X Y Z : DerivedModuleCategory A D}
    {f : X ⟶ Y} (hf : ModuleFiniteCellFactor A D S f) (g : Y ⟶ Z) :
    ModuleFiniteCellFactor A D S (f ≫ g) := by
  obtain ⟨P, hP, a, b, hab⟩ := hf
  exact ⟨P, hP, a, b ≫ g, by rw [← Category.assoc, hab]⟩

lemma ModuleFiniteCellFactor.precompose {S : Set D} {X Y Z : DerivedModuleCategory A D}
    {g : Y ⟶ Z} (hg : ModuleFiniteCellFactor A D S g) (f : X ⟶ Y) :
    ModuleFiniteCellFactor A D S (f ≫ g) := by
  obtain ⟨P, hP, a, b, hab⟩ := hg
  exact ⟨P, hP, f ≫ a, b, by rw [Category.assoc, hab]⟩

lemma ModuleFiniteCellFactor.shift {S : Set D} {X Y : DerivedModuleCategory A D}
    {f : X ⟶ Y} (hf : ModuleFiniteCellFactor A D S f) (n : ℤ) :
    ModuleFiniteCellFactor A D S (f⟦n⟧') := by
  obtain ⟨P, hP, a, b, hab⟩ := hf
  exact ⟨P⟦n⟧, (derivedFiniteCellOver A D S).le_shift n _ hP,
    a⟦n⟧', b⟦n⟧', by rw [← CategoryTheory.Functor.map_comp, hab]⟩

lemma moduleFiniteCellFactor_sum {S : Set D} {J : Type*}
    {X Y : DerivedModuleCategory A D} (t : Finset J) (f : J → (X ⟶ Y))
    (hf : ∀ j ∈ t, ModuleFiniteCellFactor A D S (f j)) :
    ModuleFiniteCellFactor A D S (∑ j ∈ t, f j) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using moduleFiniteCellFactor_zero A D S X Y
  | @insert i t hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add A D
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- compact な対象から有限 cell の任意の u-small 余積への射は有限 cell を経由する。 -/
lemma moduleCompact_coproduct_finiteCellFactor {S : Set D} {X : DerivedModuleCategory A D}
    (hX : moduleCompact A D X) {J : Type u} (F : J → DerivedModuleCategory A D)
    (hF : ∀ j, derivedFiniteCellOver A D S (F j)) (f : X ⟶ ∐ F) :
    ModuleFiniteCellFactor A D S f := by
  obtain ⟨t, g, hg⟩ := hX J F f
  rw [← hg]
  exact moduleFiniteCellFactor_sum A D t (fun j => g j ≫ Sigma.ι F j)
    (fun j _ => ⟨F j, hF j, g j, Sigma.ι F j, rfl⟩)

/-- 恒等射の有限 cell 因子分解は、既存の Perf の定義そのものである。 -/
lemma modulePerfectOver_iff_id_finiteCellFactor (S : Set D) (X : DerivedModuleCategory A D) :
    modulePerfectOver A D S X ↔ ModuleFiniteCellFactor A D S (𝟙 X) := by
  constructor
  · rintro ⟨P, hP, ⟨r⟩⟩
    exact ⟨P, hP, r.i, r.r, r.retract⟩
  · rintro ⟨P, hP, a, b, hab⟩
    exact ⟨P, hP, ⟨{ i := a, r := b, retract := hab }⟩⟩

/-- 任意の compact な始域からの射に対する有限 cell 因子分解性。 -/
def moduleFiniteCellFactorTarget (S : Set D) : ObjectProperty (DerivedModuleCategory A D) :=
  fun Y => ∀ (X : DerivedModuleCategory A D), moduleCompact A D X →
    ∀ f : X ⟶ Y, ModuleFiniteCellFactor A D S f

lemma moduleFiniteCellFactorTarget_of_finiteCell {S : Set D}
    {Y : DerivedModuleCategory A D} (hY : derivedFiniteCellOver A D S Y) :
    moduleFiniteCellFactorTarget A D S Y :=
  fun _ _ f => ⟨Y, hY, f, 𝟙 Y, Category.comp_id f⟩

lemma moduleFiniteCellFactorTarget_shift {S : Set D} {Y : DerivedModuleCategory A D}
    (hY : moduleFiniteCellFactorTarget A D S Y) (n : ℤ) :
    moduleFiniteCellFactorTarget A D S (Y⟦n⟧) := by
  intro X hX f
  let E := shiftEquiv' (DerivedModuleCategory A D) (-n) n (neg_add_cancel n)
  let e := E.toAdjunction.homEquiv X Y
  have ha := hY _ (moduleCompact_shift A D hX (-n)) (e.symm f)
  have hf := (ha.shift A D n).precompose A D (E.toAdjunction.unit.app X)
  have he : E.toAdjunction.unit.app X ≫ (e.symm f)⟦n⟧' = f :=
    (E.toAdjunction.homEquiv_unit X Y (e.symm f)).symm.trans (e.apply_symm_apply f)
  rwa [he] at hf

lemma moduleFiniteCellFactorTarget_coproduct {S : Set D} {J : Type u}
    (F : J → DerivedModuleCategory A D) (hF : ∀ j, moduleFiniteCellFactorTarget A D S (F j)) :
    moduleFiniteCellFactorTarget A D S (∐ F) := by
  intro X hX f
  obtain ⟨t, g, hg⟩ := hX J F f
  rw [← hg]
  exact moduleFiniteCellFactor_sum A D t (fun j => g j ≫ Sigma.ι F j)
    (fun j _ => (hF j X hX (g j)).postcompose A D (Sigma.ι F j))

end SerrePositivity.DifferentialGraded
end

end CompactConverseFactor

/-! ## CompactConverseExtensions（旧 SerrePositivity/DifferentialGraded/Perfect/CompactConverseExtensions.lean） -/

/-! # compact な始域からの有限 cell 因子分解の拡大閉性

Neeman 型の議論：compact な始域と有限 cell の間の射の錐を compact な補助始域とする。
有限 cell の本数を、semifree filtration の高さだけから推測しない。
-/

@[expose] public section CompactConverseExtensions
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Preadditive Pretriangulated
open scoped ZeroObject
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleFiniteCellFactorTarget_triangle_obj₂ {S : Set D}
    (T : Triangle (DerivedModuleCategory A D))
    (hT : T ∈ distTriang (DerivedModuleCategory A D))
    (h₁ : moduleFiniteCellFactorTarget A D S T.obj₁)
    (h₃ : moduleFiniteCellFactorTarget A D S T.obj₃) :
    moduleFiniteCellFactorTarget A D S T.obj₂ := by
  intro X hX f
  obtain ⟨P, hP, a, b, hab⟩ := h₃ X hX (f ≫ T.mor₂)
  obtain ⟨Z, j, k, hZ⟩ := distinguished_cocone_triangle a
  have hPc : moduleCompact A D P := modulePerfectOver_compact A D
    ((derivedFiniteCellOver A D S).le_retractClosure _ hP)
  have hZc : moduleCompact A D Z := moduleCompact_triangle_obj₃ A D _ hZ hX hPc
  have haz : a ≫ (b ≫ T.mor₃) = 0 := by
    rw [← Category.assoc, hab, Category.assoc, comp_distTriang_mor_zero₂₃ _ hT, comp_zero]
  obtain ⟨z, hz⟩ := Triangle.yoneda_exact₂ _ hZ (b ≫ T.mor₃) haz
  change b ≫ T.mor₃ = j ≫ z at hz
  obtain ⟨Q, hQ, l, m, hlm⟩ :=
    moduleFiniteCellFactorTarget_shift A D h₁ 1 Z hZc z
  let δ := j ≫ l
  obtain ⟨E, e, q, hE⟩ := distinguished_cocone_triangle₁ δ
  have hEc : derivedFiniteCellOver A D S E :=
    (derivedFiniteCellOver A D S).ext_of_isTriangulatedClosed₁ _ hE hP hQ
  have hδ : δ ≫ m = b ≫ T.mor₃ := by
    dsimp only [δ]
    rw [Category.assoc, hlm, ← hz]
  obtain ⟨u, hu, _⟩ := complete_distinguished_triangle_morphism₁ _ T.rotate hE
    (rot_of_distTriang _ hT) b m hδ
  change E ⟶ T.obj₂ at u
  change e ≫ b = u ≫ T.mor₂ at hu
  have haδ : a ≫ δ = 0 := by
    have hj : a ≫ j = 0 := comp_distTriang_mor_zero₁₂ _ hZ
    dsimp only [δ]
    rw [← Category.assoc, hj, zero_comp]
  obtain ⟨a', ha'⟩ := Triangle.coyoneda_exact₂ _ hE a haδ
  change X ⟶ E at a'
  change a = a' ≫ e at ha'
  have hdiff : (f - a' ≫ u) ≫ T.mor₂ = 0 := by
    rw [sub_comp, Category.assoc, ← hu, ← Category.assoc, ← ha', hab, sub_self]
  obtain ⟨r, hr⟩ := Triangle.coyoneda_exact₂ T hT (f - a' ≫ u) hdiff
  have hfac : ModuleFiniteCellFactor A D S (a' ≫ u) := ⟨E, hEc, a', u, rfl⟩
  have hrest : ModuleFiniteCellFactor A D S (f - a' ≫ u) := by
    rw [hr]
    exact (h₁ X hX r).postcompose A D T.mor₁
  have h := hfac.add A D hrest
  convert h using 1; abel

instance moduleFiniteCellFactorTargetClosedUnderIso (S : Set D) :
    (moduleFiniteCellFactorTarget A D S).IsClosedUnderIsomorphisms where
  of_iso e hX Y hY f := by
    have h := (hX Y hY (f ≫ e.inv)).postcompose A D e.hom
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h

instance moduleFiniteCellFactorTargetStableUnderShift (S : Set D) :
    (moduleFiniteCellFactorTarget A D S).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun _ h => moduleFiniteCellFactorTarget_shift A D h n⟩

instance moduleFiniteCellFactorTargetContainsZero (S : Set D) :
    (moduleFiniteCellFactorTarget A D S).ContainsZero :=
  ⟨⟨0, isZero_zero _, moduleFiniteCellFactorTarget_of_finiteCell A D
    ((derivedFiniteCellOver A D S).prop_zero)⟩⟩

instance moduleFiniteCellFactorTargetTriangulatedClosed₂ (S : Set D) :
    (moduleFiniteCellFactorTarget A D S).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.mk' (moduleFiniteCellFactorTarget_triangle_obj₂ A D)

instance moduleFiniteCellFactorTargetIsTriangulated (S : Set D) :
    (moduleFiniteCellFactorTarget A D S).IsTriangulated where

/-- この因子分解性は、任意の可算 telescope 三角形で閉じている。 -/
lemma moduleFiniteCellFactorTarget_telescope {S : Set D}
    (F : ℕ → DerivedModuleCategory A D) (d : ∀ n, F n ⟶ F (n + 1))
    (hF : ∀ n, moduleFiniteCellFactorTarget A D S (F n)) {Y : DerivedModuleCategory A D}
    (c : (∐ moduleTelescopeFamily A D F) ⟶ Y)
    (b : Y ⟶ (∐ moduleTelescopeFamily A D F)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (moduleTelescopeMap A D F d) c b ∈
      distTriang (DerivedModuleCategory A D)) : moduleFiniteCellFactorTarget A D S Y := by
  intro X hX f
  obtain ⟨n, g, hg⟩ := moduleCompact_telescope_factor A D F d hX c b hT f
  rw [hg]
  exact (hF n X hX g).postcompose A D (Sigma.ι (moduleTelescopeFamily A D F) ⟨n⟩ ≫ c)

lemma modulePerfectOver_of_compact_factorTarget {S : Set D} {X : DerivedModuleCategory A D}
    (hX : moduleCompact A D X) (h : moduleFiniteCellFactorTarget A D S X) :
    modulePerfectOver A D S X :=
  (modulePerfectOver_iff_id_finiteCellFactor A D S X).2 (h X hX (𝟙 X))

end SerrePositivity.DifferentialGraded
end

end CompactConverseExtensions

/-! ## CompactConverseResolutionStages（旧 SerrePositivity/DifferentialGraded/Perfect/CompactConverseResolutionStages.lean） -/

/-! # 標準解像度の有限高さの段階への有限 cell 因子分解

各段の cell の個数は有限と仮定しない。既存の実際の cone と射影余積を使う。
-/

@[expose] public section CompactConverseResolutionStages
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleFiniteCellOver_freeSphere {S : Set D} (x : D) (hx : x ∈ S) (n : ℤ) :
    moduleFiniteCellOver A D S (freeSphere A D x n) := by
  have h0 : moduleFiniteCellOver A D S (freeSphere A D x 0) :=
    moduleFiniteCellOver_of_iso A D (moduleTensorUnitIso A D (representable A x)).symm
      (moduleFiniteCellOver_representable A D x hx)
  exact moduleFiniteCellOver_of_iso A D
    (freeSphereShiftIso A D x 0 (-n) ≪≫ eqToIso
      (congrArg (freeSphere A D x) (by omega : 0 - -n = n)))
    (moduleFiniteCellOver_shift A D h0 (-n))

lemma moduleFiniteCellFactorTarget_coproduct_small {S : Set D} {J : Type w} [Small.{u} J]
    (F : J → DerivedModuleCategory A D) (hF : ∀ j, moduleFiniteCellFactorTarget A D S (F j)) :
    moduleFiniteCellFactorTarget A D S (∐ F) := by
  let e : Shrink.{u} J ≃ J := (equivShrink J).symm
  exact (moduleFiniteCellFactorTarget A D S).prop_of_iso (Sigma.reindex e F)
    (moduleFiniteCellFactorTarget_coproduct A D (F ∘ e) (fun j => hF (e j)))

lemma moduleFiniteCellFactorTarget_projectiveCoproduct {S : Set D} {J : Type w} [Small.{u} J]
    (M : J → ModuleCategory A D) (hM : ∀ j, moduleHomotopicallyProjective A D (M j))
    (hF : ∀ j, moduleFiniteCellFactorTarget A D S ((moduleToDerived A D).obj (M j))) :
    moduleFiniteCellFactorTarget A D S ((moduleToDerived A D).obj (∐ M)) := by
  let hc := colimit.isColimit (Discrete.functor (fun j => (moduleToDerived A D).obj (M j)))
  exact (moduleFiniteCellFactorTarget A D S).prop_of_iso
    (hc.coconePointUniqueUpToIso (moduleProjectiveDerivedCofanIsColimit A D M hM))
    (moduleFiniteCellFactorTarget_coproduct_small A D _ hF)

lemma moduleFiniteCellFactorTarget_sphereCoproduct {J : Type w} [Small.{u} J]
    (x : J → D) (n : J → ℤ) :
    moduleFiniteCellFactorTarget A D Set.univ
      ((moduleToDerived A D).obj (∐ fun j => freeSphere A D (x j) (n j))) :=
  moduleFiniteCellFactorTarget_projectiveCoproduct A D _
    (fun j => freeSphere_homotopicallyProjective A D (x j) (n j))
    (fun j => moduleFiniteCellFactorTarget_of_finiteCell A D
      ((moduleFiniteCellOver A D Set.univ).prop_map_obj (moduleToDerived A D)
        (moduleFiniteCellOver_freeSphere A D (x j) (Set.mem_univ _) (n j))))

lemma moduleFiniteCellFactorTarget_resolutionStage (M : ModuleCategory A D) (n : ℕ) :
    moduleFiniteCellFactorTarget A D Set.univ
      ((moduleToDerived A D).obj (moduleResolutionStage A D M n).left) := by
  induction n with
  | zero =>
    apply (moduleFiniteCellFactorTarget A D Set.univ).prop_of_isZero
    apply moduleToDerived_isZero_of_acyclic A D
    intro x i
    let : HasExactColimitsOfShape (Discrete (ModuleDiskCoverIndex A D M)) (ModuleCat.{u} A) :=
      HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
        (Discrete.equivalence (equivShrink.{u} (ModuleDiskCoverIndex A D M)).symm)
    exact (complex_colimit_acyclic A
      (Discrete.functor (moduleDiskCoverFamily A D M) ⋙ moduleEvaluation A D x)
      (fun j => freeDisk_acyclic A D j.as.1 j.as.2.1 x) i).of_iso
        (preservesColimitIso (moduleEvaluation A D x)
          (Discrete.functor (moduleDiskCoverFamily A D M))).symm
  | succ n ih =>
    exact (moduleFiniteCellFactorTarget A D Set.univ).ext_of_isTriangulatedClosed₃ _
      (moduleDerivedConeTriangle_distinguished A D
        (moduleKernelCellMap A D (moduleResolutionStage A D M n).hom))
      (moduleFiniteCellFactorTarget_sphereCoproduct A D _ _) ih

end SerrePositivity.DifferentialGraded
end

end CompactConverseResolutionStages

/-! ## CompactConverseSequential（旧 SerrePositivity/DifferentialGraded/Perfect/CompactConverseSequential.lean） -/

/-! # 可算余極限の 1-shift による cokernel 表示

三角圏での telescope と、標準 dg 解像度の実際の余極限を比較するための表示。
-/

@[expose] public section CompactConverseSequential
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Preadditive

section
variable {C : Type v} [Category.{w} C] [Preadditive C]
    (F : ℕ ⥤ C) [HasCoproduct (fun n : ULift.{u} ℕ => F.obj n.down)]

abbrev sequentialCoproductFamily (n : ULift.{u} ℕ) := F.obj n.down

def sequentialCoproductShift : (∐ sequentialCoproductFamily.{u} F) ⟶
    ∐ sequentialCoproductFamily.{u} F :=
  Sigma.desc (fun n => F.map (homOfLE (Nat.le_succ n.down)) ≫
    Sigma.ι (sequentialCoproductFamily.{u} F) ⟨n.down + 1⟩)

def sequentialCoproductMap : (∐ sequentialCoproductFamily.{u} F) ⟶
    ∐ sequentialCoproductFamily.{u} F := 𝟙 _ - sequentialCoproductShift.{u} F

def sequentialCoproductProjection (n : ℕ) :
    (∐ sequentialCoproductFamily.{u} F) ⟶ F.obj n :=
  Sigma.desc (Pi.single ⟨n⟩ (𝟙 (F.obj n)))

lemma sequentialCoproductShift_projection_zero :
    sequentialCoproductShift.{u} F ≫ sequentialCoproductProjection.{u} F 0 = 0 := by
  apply Sigma.hom_ext
  intro n
  simp [sequentialCoproductShift, sequentialCoproductProjection, Category.assoc]

lemma sequentialCoproductShift_projection_succ (n : ℕ) :
    sequentialCoproductShift.{u} F ≫ sequentialCoproductProjection.{u} F (n + 1) =
      sequentialCoproductProjection.{u} F n ≫ F.map (homOfLE (Nat.le_succ n)) := by
  apply Sigma.hom_ext
  intro ⟨i⟩
  by_cases h : i = n
  · subst i
    simp [sequentialCoproductShift, sequentialCoproductProjection, Category.assoc]
  · simp [sequentialCoproductShift, sequentialCoproductProjection, Category.assoc, h]

def sequentialCoproductDesc (s : Cocone F) : (∐ sequentialCoproductFamily.{u} F) ⟶ s.pt :=
  Sigma.desc (fun n => s.ι.app n.down)

lemma sequentialCoproductMap_desc (s : Cocone F) :
    sequentialCoproductMap.{u} F ≫ sequentialCoproductDesc.{u} F s = 0 := by
  apply Sigma.hom_ext
  intro n
  simp only [sequentialCoproductMap, sequentialCoproductShift, sequentialCoproductDesc,
    comp_sub, sub_comp, Category.id_comp, Category.assoc, Sigma.ι_comp_desc,
    Sigma.ι_comp_desc_assoc, s.w, sub_self, comp_zero]

/-- cokernel への射から元の列の cocone を復元する。 -/
def sequentialCoproductCoconeOfZero {Z : C} (f : (∐ sequentialCoproductFamily.{u} F) ⟶ Z)
    (hf : sequentialCoproductMap.{u} F ≫ f = 0) : Cocone F where
  pt := Z
  ι := NatTrans.ofSequence
    (fun n => Sigma.ι (sequentialCoproductFamily.{u} F) ⟨n⟩ ≫ f) (by
      intro n
      have h := congrArg (fun k => Sigma.ι (sequentialCoproductFamily.{u} F) ⟨n⟩ ≫ k) hf
      have he : Sigma.ι (sequentialCoproductFamily.{u} F) ⟨n⟩ ≫ f =
          F.map (homOfLE (Nat.le_succ n)) ≫
            Sigma.ι (sequentialCoproductFamily.{u} F) ⟨n + 1⟩ ≫ f := by
        simpa only [sequentialCoproductMap, sequentialCoproductShift, comp_sub, sub_comp,
          Category.comp_id, Category.assoc, Category.id_comp, Sigma.ι_comp_desc_assoc,
          comp_zero, sub_eq_zero] using h
      change F.map (homOfLE (Nat.le_succ n)) ≫
        (Sigma.ι (sequentialCoproductFamily.{u} F) ⟨n + 1⟩ ≫ f) =
          (Sigma.ι (sequentialCoproductFamily.{u} F) ⟨n⟩ ≫ f) ≫ 𝟙 Z
      rw [Category.comp_id]
      exact he.symm)

def sequentialCoproductCokernel (s : Cocone F) (hs : IsColimit s) :
    IsColimit (CokernelCofork.ofπ (sequentialCoproductDesc.{u} F s)
      (sequentialCoproductMap_desc.{u} F s)) :=
  Cofork.IsColimit.mk _
    (fun c => hs.desc (sequentialCoproductCoconeOfZero.{u} F c.π (CokernelCofork.condition c)))
    (by
      intro c
      apply Sigma.hom_ext
      intro n
      simpa only [Cofork.π_ofπ, sequentialCoproductDesc, Sigma.ι_comp_desc_assoc,
        sequentialCoproductCoconeOfZero, NatTrans.ofSequence_app] using
        hs.fac (sequentialCoproductCoconeOfZero.{u} F c.π (CokernelCofork.condition c)) n.down)
    (by
      intro c m hm
      apply hs.hom_ext
      intro n
      have h := congrArg (fun k => Sigma.ι (sequentialCoproductFamily.{u} F) ⟨n⟩ ≫ k) hm
      have hf := hs.fac (sequentialCoproductCoconeOfZero.{u} F c.π
        (CokernelCofork.condition c)) n
      simpa only [Cofork.π_ofπ, sequentialCoproductDesc, Sigma.ι_comp_desc_assoc,
        sequentialCoproductCoconeOfZero, NatTrans.ofSequence_app] using h.trans hf.symm)

/-- 加法関手に対する 1-shift の標準余積比較の可換性。 -/
lemma sequentialCoproductMap_sigmaComparison {B : Type*} [Category* B] [Preadditive B]
    (G : C ⥤ B) [G.Additive]
    [HasColimitsOfShape (Discrete (ULift.{u} ℕ)) B] :
    sequentialCoproductMap.{u} (F ⋙ G) ≫
      sigmaComparison G (sequentialCoproductFamily.{u} F) =
        sigmaComparison G (sequentialCoproductFamily.{u} F) ≫
          G.map (sequentialCoproductMap.{u} F) := by
  have hι (n : ULift.{u} ℕ) : Sigma.ι (sequentialCoproductFamily.{u} (F ⋙ G)) n ≫
      sigmaComparison G (sequentialCoproductFamily.{u} F) =
        G.map (Sigma.ι (sequentialCoproductFamily.{u} F) n) := by
    convert ι_comp_sigmaComparison G (sequentialCoproductFamily.{u} F) n using 1 <;> rfl
  apply Sigma.hom_ext
  intro n
  simp only [sequentialCoproductMap, sequentialCoproductShift, comp_sub, sub_comp,
    Category.comp_id, Category.id_comp, Category.assoc, Sigma.ι_comp_desc_assoc,
    hι, reassoc_of% hι, CategoryTheory.Functor.map_sub, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.comp_map]
  rw [← G.map_comp, ← G.map_comp]
  rw [Sigma.ι_comp_desc]

end

variable (A : Type u) [CommRing A]

/-- ModuleCat の可算 1-shift は単射。遷移射の単射性は不要。 -/
lemma sequentialCoproductMap_moduleCat_injective (F : ℕ ⥤ ModuleCat.{u} A) :
    Function.Injective (sequentialCoproductMap.{u} F) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro z hz
  have he : z = sequentialCoproductShift.{u} F z := by
    change z - sequentialCoproductShift.{u} F z = 0 at hz
    exact sub_eq_zero.mp hz
  have hp (n : ℕ) : sequentialCoproductProjection.{u} F n z = 0 := by
    induction n with
    | zero =>
      have h := congrArg (fun k => k z) (sequentialCoproductShift_projection_zero.{u} F)
      change sequentialCoproductProjection.{u} F 0 (sequentialCoproductShift.{u} F z) = 0 at h
      exact (congrArg (sequentialCoproductProjection.{u} F 0) he).trans h
    | succ n ih =>
      have h := congrArg (fun k => k z) (sequentialCoproductShift_projection_succ.{u} F n)
      change sequentialCoproductProjection.{u} F (n + 1) (sequentialCoproductShift.{u} F z) =
        F.map (homOfLE (Nat.le_succ n)) (sequentialCoproductProjection.{u} F n z) at h
      rw [ih, map_zero] at h
      exact (congrArg (sequentialCoproductProjection.{u} F (n + 1)) he).trans h
  obtain ⟨t, a, ha⟩ := moduleCofan_element_rep A (sequentialCoproductFamily.{u} F)
    (Cofan.mk _ (Sigma.ι _)) (coproductIsCoproduct _) z
  have hai (i : ULift.{u} ℕ) (hi : i ∈ t) : a i = 0 := by
    have h := congrArg (sequentialCoproductProjection.{u} F i.down) ha
    rw [map_sum, hp] at h
    rw [Finset.sum_eq_single i] at h
    · simpa [sequentialCoproductProjection, ← ModuleCat.comp_apply] using h
    · intro j _ hji
      have hij : j ≠ (⟨i.down⟩ : ULift.{u} ℕ) := by simpa using hji
      simp [sequentialCoproductProjection, ← ModuleCat.comp_apply, hij]
    · exact fun h => (h hi).elim
  rw [← ha]
  exact Finset.sum_eq_zero (fun i hi => by rw [hai i hi, map_zero])

lemma sequentialCoproductMap_moduleCat_mono (F : ℕ ⥤ ModuleCat.{u} A) :
    Mono (sequentialCoproductMap.{u} F) :=
  (ModuleCat.mono_iff_injective _).2 (sequentialCoproductMap_moduleCat_injective A F)

lemma sequentialCoproductMap_mono_of_moduleCat_functor
    {C : Type v} [Category.{w} C] [Preadditive C] (F : ℕ ⥤ C)
    [HasCoproduct (sequentialCoproductFamily.{u} F)]
    (G : C ⥤ ModuleCat.{u} A) [G.Additive]
    [PreservesColimit (Discrete.functor (sequentialCoproductFamily.{u} F)) G] :
    Mono (G.map (sequentialCoproductMap.{u} F)) := by
  have : Mono (sequentialCoproductMap.{u} (F ⋙ G)) :=
    sequentialCoproductMap_moduleCat_mono A _
  apply (mono_comp_iff_of_isIso (sigmaComparison G (sequentialCoproductFamily.{u} F)) _).1
  rw [← sequentialCoproductMap_sigmaComparison]
  infer_instance

end SerrePositivity.DifferentialGraded
end

end CompactConverseSequential

/-! ## CompactConverseSequentialCone（旧 SerrePositivity/DifferentialGraded/Perfect/CompactConverseSequentialCone.lean） -/

/-! # dg 加群の可算余極限と telescope cone の擬同型

次数ごとの 1-shift の単射性と cokernel の普遍性を用いる。遷移射の単射性は不要。
-/

@[expose] public section CompactConverseSequentialCone
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex CochainComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (F : ℕ ⥤ ModuleCategory A D) (s : Cocone F)

def moduleSequentialShortComplex : ShortComplex (ModuleCategory A D) :=
  ShortComplex.mk (sequentialCoproductMap.{u} F) (sequentialCoproductDesc.{u} F s)
    (sequentialCoproductMap_desc.{u} F s)

lemma moduleSequentialShortComplex_evaluation_shortExact (hs : IsColimit s) (x : D) :
    ((moduleSequentialShortComplex A D F s).map (moduleEvaluation A D x)).ShortExact := by
  let E := moduleEvaluation A D x
  let S := (moduleSequentialShortComplex A D F s).map E
  have hc : IsColimit (CokernelCofork.ofπ S.g S.zero) :=
    (isColimitMapCoconeCoforkEquiv' E (sequentialCoproductMap_desc.{u} F s)).toFun
      (isColimitOfPreserves E (sequentialCoproductCokernel.{u} F s hs))
  have hm : Mono S.f := by
    apply HomologicalComplex.mono_of_mono_f
    intro n
    exact sequentialCoproductMap_mono_of_moduleCat_functor A F
      (E ⋙ HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) n)
  exact {
    exact := S.exact_of_g_is_cokernel hc
    mono_f := hm
    epi_g := epi_of_isColimit_cofork hc }

def moduleSequentialConeDesc : moduleCone A D (sequentialCoproductMap.{u} F) ⟶ s.pt :=
  moduleConeDesc A D _ _ (sequentialCoproductMap_desc.{u} F s)

set_option maxHeartbeats 800000 in
-- 評価された豊穣加群 cone と通常の mapping cone の型の定義展開に必要。
lemma moduleSequentialConeDesc_quasiIso (hs : IsColimit s) :
    moduleQuasiIso A D (moduleSequentialConeDesc A D F s) := by
  intro x
  dsimp only [moduleSequentialConeDesc]
  rw [moduleConeDesc_eval]
  have h := mappingCone.quasiIso_descShortComplex
    (moduleSequentialShortComplex_evaluation_shortExact A D F s hs x)
  convert h using 1 <;> rfl

end SerrePositivity.DifferentialGraded
end

end CompactConverseSequentialCone

/-! ## CompactConverse（旧 SerrePositivity/DifferentialGraded/Perfect/CompactConverse.lean） -/

/-! # compact ⇒ Perf：引用なしの標準解像度による証明

標準解像度の各段、射影余積、cone に対する有限因子分解性と、
可算余極限の cone 表示を組み合わせる。係数環の体性・Hom の平坦性は仮定しない。
-/

@[expose] public section CompactConverse
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 標準解像度の余極限に対する有限 cell 因子分解性。 -/
lemma moduleFiniteCellFactorTarget_resolutionCandidate (M : ModuleCategory A D) :
    moduleFiniteCellFactorTarget A D Set.univ
      ((moduleToDerived A D).obj (moduleResolutionCandidate A D M)) := by
  let F := moduleResolutionDiagram A D M
  let P := sequentialCoproductFamily.{u} F
  have hp (j : ULift.{u} ℕ) : moduleHomotopicallyProjective A D (P j) :=
    (moduleResolutionSemifreeFiltration A D M).stage_homotopicallyProjective A D (j.down + 1)
  have hP : moduleFiniteCellFactorTarget A D Set.univ ((moduleToDerived A D).obj (∐ P)) :=
    moduleFiniteCellFactorTarget_projectiveCoproduct A D P hp
      (fun j => moduleFiniteCellFactorTarget_resolutionStage A D M j.down)
  have hcone : moduleFiniteCellFactorTarget A D Set.univ
      ((moduleToDerived A D).obj (moduleCone A D (sequentialCoproductMap.{u} F))) :=
    (moduleFiniteCellFactorTarget A D Set.univ).ext_of_isTriangulatedClosed₃ _
      (moduleDerivedConeTriangle_distinguished A D (sequentialCoproductMap.{u} F)) hP hP
  exact (moduleFiniteCellFactorTarget A D Set.univ).prop_of_iso
    (moduleDerivedIso A D (moduleSequentialConeDesc A D F (colimit.cocone F))
      (moduleSequentialConeDesc_quasiIso A D F (colimit.cocone F) (colimit.isColimit F))) hcone

/-- 任意の主導来対象へ compact な始域から向かう射は有限 cell を経由する。 -/
lemma moduleFiniteCellFactorTarget_all (X : DerivedModuleCategory A D) :
    moduleFiniteCellFactorTarget A D Set.univ X := by
  obtain ⟨⟨M⟩⟩ := X
  exact (moduleFiniteCellFactorTarget A D Set.univ).prop_of_iso
    (moduleDerivedIso A D (moduleResolutionCandidateπ A D M)
      (moduleResolutionCandidateπ_quasiIso A D M))
    (moduleFiniteCellFactorTarget_resolutionCandidate A D M)

/-- U13d：u-small 余積に関して compact な対象は perfect。 -/
lemma moduleCompact_perfect {X : DerivedModuleCategory A D} (hX : moduleCompact A D X) :
    modulePerfect A D X :=
  modulePerfectOver_of_compact_factorTarget A D hX (moduleFiniteCellFactorTarget_all A D X)

lemma moduleCompact_iff_perfect (X : DerivedModuleCategory A D) :
    moduleCompact A D X ↔ modulePerfect A D X :=
  ⟨moduleCompact_perfect A D, modulePerfect_compact A D⟩

end SerrePositivity.DifferentialGraded
end

end CompactConverse

/-! ## SmallEnhancementTriangulated（旧 SerrePositivity/DifferentialGraded/Perfect/SmallEnhancementTriangulated.lean） -/

/-! # 小さいperfect dg代表系のH⁰三角構造

小さい代表系ではshift後の加群を選択した代表へ戻す。
全Homを保つdg包含との比較は別に整合性を与える。
-/

@[expose] public section SmallEnhancementTriangulated
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 小さい射影的perfect dg代表系の実際のH⁰。 -/
abbrev SmallPerfectDGHomotopyCategoryOver (S : Set D) :=
  HomotopyCategory A (SmallPerfectDGModuleOver A D S)

/-- 主Perfでshiftした後、選択した小さい射影的代表へ戻るH⁰関手。 -/
def smallPerfectDGShiftHomotopyFunctor (S : Set D) (s : ℤ) :
    SmallPerfectDGHomotopyCategoryOver A D S ⥤ SmallPerfectDGHomotopyCategoryOver A D S :=
  (smallPerfectDGModuleHomotopyEquivalence A D S).functor ⋙
    shiftFunctor (PerfectModuleCategoryOver A D S) s ⋙
      (smallPerfectDGModuleHomotopyEquivalence A D S).inverse

/-- 代表を取り直したshiftの主Perf比較は、同値の余単位から構成する。 -/
def smallPerfectDGShiftHomotopyIso (S : Set D) (s : ℤ) :
    smallPerfectDGShiftHomotopyFunctor A D S s ⋙
      (smallPerfectDGModuleHomotopyEquivalence A D S).functor ≅
    (smallPerfectDGModuleHomotopyEquivalence A D S).functor ⋙
      shiftFunctor (PerfectModuleCategoryOver A D S) s := by
  let e := smallPerfectDGModuleHomotopyEquivalence A D S
  exact Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft e.functor
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (shiftFunctor (PerfectModuleCategoryOver A D S) s) e.counitIso ≪≫
      (shiftFunctor (PerfectModuleCategoryOver A D S) s).rightUnitor)

/-- 小さいH⁰のshiftにzero/add coherenceを誘導し、対象の代表選択を整合させる。 -/
instance smallPerfectDGHomotopyHasShift (S : Set D) :
    HasShift (SmallPerfectDGHomotopyCategoryOver A D S) ℤ :=
  (Functor.FullyFaithful.ofFullyFaithful
    (smallPerfectDGModuleHomotopyEquivalence A D S).functor).hasShift
      (smallPerfectDGShiftHomotopyFunctor A D S) (smallPerfectDGShiftHomotopyIso A D S)

/-- 誘導した各shift関手は、定義した代表取り直し関手そのものである。 -/
lemma smallPerfectDGHomotopy_shiftFunctor (S : Set D) (s : ℤ) :
    shiftFunctor (SmallPerfectDGHomotopyCategoryOver A D S) s =
      smallPerfectDGShiftHomotopyFunctor A D S s := rfl

/-- 小さい代表系の各整数shiftは加法的である。 -/
instance smallPerfectDGHomotopyShiftAdditive (S : Set D) (s : ℤ) :
    (shiftFunctor (SmallPerfectDGHomotopyCategoryOver A D S) s).Additive := by
  rw [smallPerfectDGHomotopy_shiftFunctor]
  dsimp [smallPerfectDGShiftHomotopyFunctor]
  infer_instance

/-- 小さいH⁰と主Perfの同値の順関手は誘導shiftと整合する。 -/
instance smallPerfectDGModuleHomotopyEquivalenceFunctorCommShift (S : Set D) :
    (smallPerfectDGModuleHomotopyEquivalence A D S).functor.CommShift ℤ :=
  Functor.CommShift.ofHasShiftOfFullyFaithful
    (Functor.FullyFaithful.ofFullyFaithful
      (smallPerfectDGModuleHomotopyEquivalence A D S).functor)
    (smallPerfectDGShiftHomotopyFunctor A D S) (smallPerfectDGShiftHomotopyIso A D S)

/-- 小さいH⁰同値の逆関手のshift比較を、順関手の比較から随伴で構成する。 -/
instance smallPerfectDGModuleHomotopyEquivalenceInverseCommShift (S : Set D) :
    (smallPerfectDGModuleHomotopyEquivalence A D S).inverse.CommShift ℤ :=
  (smallPerfectDGModuleHomotopyEquivalence A D S).commShiftInverse ℤ

/-- 小さいH⁰同値の単位・余単位もshiftに整合する。 -/
instance smallPerfectDGModuleHomotopyEquivalenceCommShift (S : Set D) :
    (smallPerfectDGModuleHomotopyEquivalence A D S).CommShift ℤ :=
  (smallPerfectDGModuleHomotopyEquivalence A D S).commShift_of_functor ℤ

/-- 元の小さい代表比較に同じ整合的shift比較を公開する。 -/
instance smallPerfectDGModuleToPerfectCommShift (S : Set D) :
    (smallPerfectDGModuleToPerfect A D S).CommShift ℤ :=
  smallPerfectDGModuleHomotopyEquivalenceFunctorCommShift A D S

/-- 主Perfの零対象を選択した小さい代表へ戻す。 -/
instance smallPerfectDGHomotopyHasZeroObject (S : Set D) :
    HasZeroObject (SmallPerfectDGHomotopyCategoryOver A D S) :=
  dgComparisonHasZeroObject (smallPerfectDGModuleHomotopyEquivalence A D S)

/-- 誘導shiftの下で主Perfのdistinguished三角形を引き戻す。 -/
instance smallPerfectDGHomotopyPretriangulated (S : Set D) :
    Pretriangulated (SmallPerfectDGHomotopyCategoryOver A D S) :=
  dgComparisonPretriangulated (smallPerfectDGModuleHomotopyEquivalence A D S)

/-- 小さいH⁰比較は、定義した三角構造について三角関手となる。 -/
instance smallPerfectDGModuleToPerfectIsTriangulated (S : Set D) :
    (smallPerfectDGModuleToPerfect A D S).IsTriangulated where
  map_distinguished _ hT := hT

/-- 小さいH⁰の八面体公理は、主Perfへの完全忠実比較で反映する。 -/
instance smallPerfectDGHomotopyIsTriangulated (S : Set D) :
    IsTriangulated (SmallPerfectDGHomotopyCategoryOver A D S) :=
  IsTriangulated.of_fully_faithful_triangulated_functor (smallPerfectDGModuleToPerfect A D S)

/-- 小さいdg代表系のH⁰と主Perfの同値は、shift整合的な三角同値である。 -/
instance smallPerfectDGModuleHomotopyEquivalenceIsTriangulated (S : Set D) :
    (smallPerfectDGModuleHomotopyEquivalence A D S).IsTriangulated :=
  Equivalence.IsTriangulated.mk' _ (by
    change (smallPerfectDGModuleToPerfect A D S).IsTriangulated
    infer_instance)

/-- 小さい代表のH⁰包含と全射影的比較の合成は、元の小さいPerf比較そのものである。 -/
def smallPerfectDGModuleInclusionPerfectIso (S : Set D) :
    (smallPerfectDGModuleInclusion A D S).onHomotopy ⋙ perfectDGModuleToPerfect A D S ≅
      smallPerfectDGModuleToPerfect A D S := Iso.refl _

/-- 小さい代表の実際のdg包含は、H⁰で双方の整数shiftと整合する。 -/
instance smallPerfectDGModuleInclusionHomotopyCommShift (S : Set D) :
    (smallPerfectDGModuleInclusion A D S).onHomotopy.CommShift ℤ :=
  Functor.CommShift.ofComp (smallPerfectDGModuleInclusionPerfectIso A D S) ℤ

/-- 小さい比較の因子化の自然同型もzero/add coherenceを保つ。 -/
instance smallPerfectDGModuleInclusionPerfectIsoCommShift (S : Set D) :
    NatTrans.CommShift (smallPerfectDGModuleInclusionPerfectIso A D S).hom ℤ :=
  Functor.CommShift.ofComp_compatibility (smallPerfectDGModuleInclusionPerfectIso A D S) ℤ

/-- 小さい代表系のH⁰包含は三角関手。主Perfへの完全忠実比較で判定する。 -/
instance smallPerfectDGModuleInclusionHomotopyIsTriangulated (S : Set D) :
    (smallPerfectDGModuleInclusion A D S).onHomotopy.IsTriangulated :=
  (Functor.isTriangulated_iff_comp_right
    (smallPerfectDGModuleInclusionPerfectIso A D S)).mpr inferInstance

/-- 小さい代表系のH⁰包含は、既に証明した完全忠実性と本質的全射性により同値である。 -/
instance smallPerfectDGModuleInclusionHomotopyIsEquivalence (S : Set D) :
    (smallPerfectDGModuleInclusion A D S).onHomotopy.IsEquivalence where

end SerrePositivity.DifferentialGraded
end

end SmallEnhancementTriangulated

/-! ## EnhancementIdempotents（旧 SerrePositivity/DifferentialGraded/Perfect/EnhancementIdempotents.lean） -/

/-! # 実際の射影的perfect dg enhancement内のホモトピー冪等元の分裂

分裂対象は実際の射影的perfect dg加群である。一対象環での有界有限射影複体代表は別途必要。
-/

@[expose] public section EnhancementIdempotents
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance perfectDGHomotopyIsIdempotentComplete (S : Set D) :
    IsIdempotentComplete (PerfectDGHomotopyCategoryOver A D S) :=
  Idempotents.Equivalence.isIdempotentComplete
    (perfectDGModuleHomotopyEquivalence A D S).symm inferInstance

instance smallPerfectDGHomotopyIsIdempotentComplete (S : Set D) :
    IsIdempotentComplete (SmallPerfectDGHomotopyCategoryOver A D S) :=
  Idempotents.Equivalence.isIdempotentComplete
    (smallPerfectDGModuleHomotopyEquivalence A D S).symm inferInstance

lemma perfectDGModule_idempotent_splits (S : Set D)
    (X : PerfectDGHomotopyCategoryOver A D S) (p : X ⟶ X) (hp : p ≫ p = p) :
    ∃ (Y : PerfectDGHomotopyCategoryOver A D S) (i : Y ⟶ X) (r : X ⟶ Y),
      i ≫ r = 𝟙 Y ∧ r ≫ i = p :=
  IsIdempotentComplete.idempotents_split X p hp

/-- 閉零射の冪等性を境界関係までで仮定し、実際の閉零分裂射を返す。 -/
lemma perfectDGModule_homotopyIdempotent_splits (S : Set D)
    (X : ClosedCategory A (PerfectDGModuleOver A D S)) (p : X ⟶ X)
    (hp : boundaryRelation A (PerfectDGModuleOver A D S) (p ≫ p) p) :
    ∃ (Y : ClosedCategory A (PerfectDGModuleOver A D S)) (i : Y ⟶ X) (r : X ⟶ Y),
      boundaryRelation A (PerfectDGModuleOver A D S) (i ≫ r) (𝟙 Y) ∧
      boundaryRelation A (PerfectDGModuleOver A D S) (r ≫ i) p := by
  let Q := toHomotopy A (PerfectDGModuleOver A D S)
  have hp' : Q.map p ≫ Q.map p = Q.map p :=
    (Q.map_comp p p).symm.trans ((toHomotopy_map_eq_iff A _ _ _).2 hp)
  obtain ⟨Y, i, r, hir, hri⟩ := perfectDGModule_idempotent_splits A D S (Q.obj X) (Q.map p) hp'
  obtain ⟨i', hi⟩ := Q.map_surjective i
  obtain ⟨r', hr⟩ := Q.map_surjective r
  refine ⟨Y.as, i', r', ?_, ?_⟩
  · apply (toHomotopy_map_eq_iff A _ _ _).1
    rw [Q.map_comp, hi, hr, hir, Q.map_id]
    rfl
  · apply (toHomotopy_map_eq_iff A _ _ _).1
    rw [Q.map_comp, hi, hr, hri]

end SerrePositivity.DifferentialGraded
end

end EnhancementIdempotents

/-! ## RingPerfectEquivalence（旧 SerrePositivity/DifferentialGraded/Perfect/RingPerfectEquivalence.lean） -/

/-! # 既存PerfectHomotopyと一対象主Perfの同値、およびホモトピー冪等分裂

元の比較関手に本質的全射性を証明する。Karoubi包絡による置換は行わない。
-/

@[expose] public section RingPerfectEquivalence
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A]
local instance : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

def ringStrictPerfectHomotopyDerivedIso (K : Complex A) (hK : strictlyPerfectComplex A K) :
    (perfectHomotopyToDGDerived A).obj (perfectHomotopyObj A K hK) ≅
      (moduleToDerived A PUnit.{1}).obj ((complexToRingModule A).obj K) :=
  (perfectHomotopyToDGDerivedCanonicalIso A).app (perfectHomotopyObj A K hK) ≪≫
    (ringDerivedEquivalence A).inverse.mapIso
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app K) ≪≫
        ringComplexDerivedUnitIso A K

instance perfectHomotopyToDGPerfectEssSurj : (perfectHomotopyToDGPerfect A).EssSurj where
  mem_essImage X := by
    obtain ⟨K, hK, ⟨eK⟩⟩ := modulePerfect_ring_has_strictlyPerfectRepresentative A X.property
    let P := perfectHomotopyObj A K hK
    refine ⟨P, ⟨(modulePerfect A PUnit.{1}).isoMk ?_⟩⟩
    exact (perfectHomotopyToDGPerfectCompInclusion A).app P ≪≫
      ringStrictPerfectHomotopyDerivedIso A K hK ≪≫ eK

instance perfectHomotopyToDGPerfectIsEquivalence :
    (perfectHomotopyToDGPerfect A).IsEquivalence where

def ringPerfectHomotopyEquivalence : PerfectHomotopy A ≌ PerfectModuleCategory A PUnit.{1} :=
  (perfectHomotopyToDGPerfect A).asEquivalence

lemma ringPerfectHomotopyEquivalence_functor :
    (ringPerfectHomotopyEquivalence A).functor = perfectHomotopyToDGPerfect A := rfl

instance ringPerfectHomotopyEquivalenceFunctorLinear :
    (ringPerfectHomotopyEquivalence A).functor.Linear A :=
  inferInstanceAs ((perfectHomotopyToDGPerfect A).Linear A)

instance ringPerfectHomotopyEquivalenceInverseLinear :
    (ringPerfectHomotopyEquivalence A).inverse.Linear A := inferInstance

instance ringPerfectHomotopyEquivalenceFunctorCommShift :
    (ringPerfectHomotopyEquivalence A).functor.CommShift ℤ :=
  inferInstanceAs ((perfectHomotopyToDGPerfect A).CommShift ℤ)

instance ringPerfectHomotopyEquivalenceInverseCommShift :
    (ringPerfectHomotopyEquivalence A).inverse.CommShift ℤ :=
  (ringPerfectHomotopyEquivalence A).commShiftInverse ℤ

instance ringPerfectHomotopyEquivalenceCommShift :
    (ringPerfectHomotopyEquivalence A).CommShift ℤ :=
  (ringPerfectHomotopyEquivalence A).commShift_of_functor ℤ

instance ringPerfectHomotopyEquivalenceIsTriangulated :
    (ringPerfectHomotopyEquivalence A).IsTriangulated :=
  Equivalence.IsTriangulated.mk' _
    (inferInstanceAs ((perfectHomotopyToDGPerfect A).IsTriangulated))

instance perfectHomotopyIsIdempotentComplete : IsIdempotentComplete (PerfectHomotopy A) :=
  Idempotents.Equivalence.isIdempotentComplete (ringPerfectHomotopyEquivalence A).symm inferInstance

lemma perfectHomotopy_idempotent_splits_complex (X : PerfectHomotopy A) (p : X ⟶ X)
    (hp : p ≫ p = p) :
    ∃ (K : Complex A) (hK : strictlyPerfectComplex A K)
      (i : perfectHomotopyObj A K hK ⟶ X) (r : X ⟶ perfectHomotopyObj A K hK),
      i ≫ r = 𝟙 _ ∧ r ≫ i = p := by
  obtain ⟨Y, i, r, hir, hri⟩ := IsIdempotentComplete.idempotents_split X p hp
  let K : Complex A := Y.obj.as
  have hK : strictlyPerfectComplex A K := (perfectHomotopyProperty_quotient A K).1 Y.property
  exact ⟨K, hK, i, r, hir, hri⟩

instance strictPerfectDGComplexToDGPerfectEssSurj :
    (strictPerfectDGComplexToDGPerfect A).EssSurj where
  mem_essImage X := by
    obtain ⟨P, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (perfectHomotopyToDGPerfect A) X
    exact ⟨(strictPerfectDGComplexHomotopyEquivalence A).inverse.obj P, ⟨e⟩⟩

instance strictPerfectDGComplexToPerfectDGHomotopyEssSurj :
    (strictPerfectDGComplexToPerfectDG A).onHomotopy.EssSurj := by
  let F := (strictPerfectDGComplexToPerfectDG A).onHomotopy
  let G := perfectDGModuleToPerfect A PUnit.{1} Set.univ
  have : (F ⋙ G).EssSurj := inferInstanceAs ((strictPerfectDGComplexToDGPerfect A).EssSurj)
  exact Functor.essSurj_of_comp_fully_faithful F G

lemma strictPerfectDGComplexToPerfectDG_homQuasiIso :
    HomQuasiIso (strictPerfectDGComplexToPerfectDG A) := by
  intro P K
  change QuasiIso (ringConstantHomIso A P.val K.val).inv
  infer_instance

lemma strictPerfectDGComplexToPerfectDG_quasiEquivalence :
    QuasiEquivalence (strictPerfectDGComplexToPerfectDG A) :=
  ⟨strictPerfectDGComplexToPerfectDG_homQuasiIso A, inferInstance⟩

end SerrePositivity.DifferentialGraded
end

end RingPerfectEquivalence

/-! ## RingPerfectCoherence（旧 SerrePositivity/DifferentialGraded/Perfect/RingPerfectCoherence.lean） -/

/-! # 有限射影の閉零冪等分裂と元の比較同値の導来・shift・三角図式 -/

@[expose] public section RingPerfectCoherence
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A]

instance strictPerfectDGComplexHomotopyIsIdempotentComplete :
    IsIdempotentComplete (HomotopyCategory A (StrictPerfectDGComplex A)) :=
  Idempotents.Equivalence.isIdempotentComplete
    (strictPerfectDGComplexHomotopyEquivalence A).symm inferInstance

/-- 閉零射のホモトピー冪等元を、実際の有界有限射影複体と閉零射で分裂する。 -/
lemma strictPerfectDGComplex_homotopyIdempotent_splits
    (X : ClosedCategory A (StrictPerfectDGComplex A)) (p : X ⟶ X)
    (hp : boundaryRelation A (StrictPerfectDGComplex A) (p ≫ p) p) :
    ∃ (Y : ClosedCategory A (StrictPerfectDGComplex A)) (i : Y ⟶ X) (r : X ⟶ Y),
      boundaryRelation A (StrictPerfectDGComplex A) (i ≫ r) (𝟙 Y) ∧
      boundaryRelation A (StrictPerfectDGComplex A) (r ≫ i) p := by
  let Q := toHomotopy A (StrictPerfectDGComplex A)
  have hp' : Q.map p ≫ Q.map p = Q.map p :=
    (Q.map_comp p p).symm.trans ((toHomotopy_map_eq_iff A _ _ _).2 hp)
  obtain ⟨Y, i, r, hir, hri⟩ :=
    IsIdempotentComplete.idempotents_split (Q.obj X) (Q.map p) hp'
  obtain ⟨i', hi⟩ := Q.map_surjective i
  obtain ⟨r', hr⟩ := Q.map_surjective r
  refine ⟨Y.as, i', r', ?_, ?_⟩
  · apply (toHomotopy_map_eq_iff A _ _ _).1
    rw [Q.map_comp, hi, hr, hir, Q.map_id]
    rfl
  · apply (toHomotopy_map_eq_iff A _ _ _).1
    rw [Q.map_comp, hi, hr, hri]

/-- 新しい同値の順関手は元の比較なので、主導来包含との既存の自然同型を保つ。 -/
def ringPerfectHomotopyEquivalenceDerivedIso :
    (ringPerfectHomotopyEquivalence A).functor ⋙
      perfectModuleInclusion A PUnit.{1} Set.univ ≅ perfectHomotopyToDGDerived A :=
  perfectHomotopyToDGPerfectCompInclusion A

instance ringPerfectHomotopyEquivalenceDerivedIsoCommShift :
    NatTrans.CommShift (ringPerfectHomotopyEquivalenceDerivedIso A).hom ℤ :=
  inferInstanceAs
    (NatTrans.CommShift (perfectHomotopyToDGPerfectCompInclusion A).hom ℤ)

/-- 同じ自然同型で三角形の比較図式も可換になる。 -/
def ringPerfectHomotopyEquivalenceTriangleIso :
    (ringPerfectHomotopyEquivalence A).functor.mapTriangle ⋙
      (perfectModuleInclusion A PUnit.{1} Set.univ).mapTriangle ≅
        (perfectHomotopyToDGDerived A).mapTriangle :=
  (Functor.mapTriangleCompIso _ _).symm ≪≫
    Functor.mapTriangleIso (ringPerfectHomotopyEquivalenceDerivedIso A)

instance ringPerfectHomotopyEquivalenceUnitCommShift :
    NatTrans.CommShift (ringPerfectHomotopyEquivalence A).unitIso.hom ℤ := inferInstance

instance ringPerfectHomotopyEquivalenceCounitCommShift :
    NatTrans.CommShift (ringPerfectHomotopyEquivalence A).counitIso.hom ℤ := inferInstance

/-- 分裂したretractの二つの等式は、元の主Perf比較の下でも同じ冪等元を与える。 -/
lemma perfectHomotopy_idempotent_splits_comparison (X : PerfectHomotopy A) (p : X ⟶ X)
    (hp : p ≫ p = p) :
    ∃ (K : Complex A) (hK : strictlyPerfectComplex A K)
      (i : perfectHomotopyObj A K hK ⟶ X) (r : X ⟶ perfectHomotopyObj A K hK),
      i ≫ r = 𝟙 _ ∧ r ≫ i = p ∧
      (perfectHomotopyToDGPerfect A).map i ≫ (perfectHomotopyToDGPerfect A).map r = 𝟙 _ ∧
      (perfectHomotopyToDGPerfect A).map r ≫ (perfectHomotopyToDGPerfect A).map i =
        (perfectHomotopyToDGPerfect A).map p := by
  obtain ⟨K, hK, i, r, hir, hri⟩ := perfectHomotopy_idempotent_splits_complex A X p hp
  refine ⟨K, hK, i, r, hir, hri, ?_, ?_⟩
  · rw [← Functor.map_comp, hir]
    exact (perfectHomotopyToDGPerfect A).map_id _
  · rw [← Functor.map_comp, hri]

end SerrePositivity.DifferentialGraded
end

end RingPerfectCoherence

/-! ## RingKaroubiFactors（旧 SerrePositivity/DifferentialGraded/Perfect/RingKaroubiFactors.lean） -/

/-! # Karoubi実現の元の比較への因子化と整数shiftの整合性 -/

@[expose] public section RingKaroubiFactors
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Idempotents
variable (A : Type u) [CommRing A]

/-- 元の比較への因子化をtoKaroubiで送ると、既存延長の比較と実現比較の合成になる。 -/
lemma ringPerfectKaroubi_fac_whisker :
    Functor.whiskerRight (ringPerfectKaroubiRealization_fac A).hom
      (toKaroubi (PerfectModuleCategory A PUnit.{1})) =
    (Functor.associator (toKaroubi (PerfectHomotopy A)) (ringPerfectKaroubiRealization A)
      (toKaroubi (PerfectModuleCategory A PUnit.{1}))).hom ≫
    Functor.whiskerLeft (toKaroubi (PerfectHomotopy A))
      (ringPerfectKaroubiRealizationToKaroubiIso A).hom ≫
    ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app
      (perfectHomotopyToDGPerfect A)).hom := by
  exact equivalenceExtension_factor_whisker (toKaroubi (PerfectHomotopy A))
    (ringPerfectKaroubiFunctor A) (perfectHomotopyToDGPerfect A)
    (toKaroubiEquivalence (PerfectModuleCategory A PUnit.{1}))
    ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app
      (perfectHomotopyToDGPerfect A))

/-- 実際のKaroubi実現と元の有限射影比較を結ぶ自然同型は整数shiftと整合する。 -/
instance ringPerfectKaroubiRealizationFacCommShift :
    NatTrans.CommShift (ringPerfectKaroubiRealization_fac A).hom ℤ := by
  refine NatTrans.CommShift.of_comp_faithful
    (G := toKaroubi (PerfectModuleCategory A PUnit.{1})) ?_
  rw [ringPerfectKaroubi_fac_whisker]
  infer_instance

/-- 三角形関手としても、Karoubi実現は元の有限射影比較へ自然に制限する。 -/
def ringPerfectKaroubiRealizationTriangleIso :
    (toKaroubi (PerfectHomotopy A)).mapTriangle ⋙ (ringPerfectKaroubiRealization A).mapTriangle ≅
      (perfectHomotopyToDGPerfect A).mapTriangle :=
  (Functor.mapTriangleCompIso _ _).symm ≪≫
    Functor.mapTriangleIso (ringPerfectKaroubiRealization_fac A)

/-- 主導来包含を経由するKaroubi比較は既存PerfectHomotopyの主導来比較に戻る。 -/
def ringPerfectKaroubiRealizationDerivedIso :
    toKaroubi (PerfectHomotopy A) ⋙
      (ringPerfectKaroubiRealization A ⋙ perfectModuleInclusion A PUnit.{1} Set.univ) ≅
      perfectHomotopyToDGDerived A :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (ringPerfectKaroubiRealization_fac A)
      (perfectModuleInclusion A PUnit.{1} Set.univ) ≪≫
    perfectHomotopyToDGPerfectCompInclusion A

instance ringPerfectKaroubiRealizationDerivedIsoCommShift :
    NatTrans.CommShift (ringPerfectKaroubiRealizationDerivedIso A).hom ℤ := by
  have : NatTrans.CommShift (Functor.isoWhiskerRight (ringPerfectKaroubiRealization_fac A)
      (perfectModuleInclusion A PUnit.{1} Set.univ)).hom ℤ := by
    change NatTrans.CommShift (Functor.whiskerRight (ringPerfectKaroubiRealization_fac A).hom _) ℤ
    infer_instance
  dsimp only [ringPerfectKaroubiRealizationDerivedIso, Iso.trans_hom, Iso.symm_hom]
  infer_instance

end SerrePositivity.DifferentialGraded
end

end RingKaroubiFactors

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "7.2.4.2" (partial := component) "仮定：可換環上の小さい dg 圏と全通常導来加群（Lean が強い：この dg 導来模型の場合）。結論：通常の三角圏の compact 性と perfect 性の同値、代表加群のシフトの compact 性と零対象の検出を示す（HA の compact・perfect と生成の通常の部分に一致）。∞ filtered 余極限による compact 性と環スペクトルへの比較は含まれない。"] _root_.SerrePositivity.DifferentialGraded.moduleCompact_iff_perfect
attribute [cite HA "7.2.4.4" (partial := component) "仮定：可換環上の小さい dg 圏の通常導来対象（Lean が強い：この dg 導来模型の場合）。結論：perfect 性と通常の compact 性を同値にする（(1) と (2) の通常の部分に一致）。M∨⊗R− による ∞ 写像空間の表現と双対の perfect 性は含まれない。"] _root_.SerrePositivity.DifferentialGraded.moduleCompact_iff_perfect
attribute [cite KST "Prop 2.9" (partial := component) "仮定：可換基礎環上の dg 加群圏で半自由模型の条件を用いる（Lean が強い）。結論：アフィンに類似する dg 加群でコンパクト性と完全性の同値。通常スキーム一般での TT との比較や qcqs の QCoh の生成性は別（Lean が弱い）。"] _root_.SerrePositivity.DifferentialGraded.moduleCompact_iff_perfect
attribute [cite KST "Rem 2.8" (partial := component) "仮定：可換基礎環上の dg 加群圏で半自由模型の条件を用いる（Lean が強い）。結論：アフィンに類似する dg 加群でコンパクト性と完全性の同値。通常スキーム一般での TT との比較や qcqs の QCoh の生成性は別（Lean が弱い）。"] _root_.SerrePositivity.DifferentialGraded.moduleCompact_iff_perfect
