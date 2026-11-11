module
public import SerrePositivity.DifferentialGraded.Complexes.HomLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.QuasiIso

/-! # 準同型な鎖写像の全射準同型による比較

概要：任意の鎖写像を、二つの次数ごと全射な射と実切断で比較する。
方針：標的の恒等射の shifted cone を直和し、収縮する因子で全射性を得る。
規約：非有界・任意可換環、模型圏の仮定なし。使われ方：pinched Hom の一般準同型不変性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded CochainComplex HomologicalComplex
variable {A : Type u} [CommRing A] {K L : Complex A}

/-- 恒等射の shifted cone は実際に収縮する。 -/
def identityCoconeContraction (L : Complex A) :
    Homotopy (𝟙 (mappingCocone (𝟙 L))) 0 := by
  let h : Homotopy (𝟙 (mappingCone (𝟙 L))) 0 :=
    mappingCone.liftHomotopy _ _ _ (mappingCone.snd _) 0 (by simp) (by simp)
  let S := CategoryTheory.shiftFunctor (Complex A) (-1)
  have h' : Homotopy (S.map (𝟙 (mappingCone (𝟙 L)))) (S.map 0) := h.shift (-1)
  exact (Homotopy.ofEq (S.map_id _).symm).trans
    (h'.trans (Homotopy.ofEq (S.map_zero _ _)))

/-- 標的の恒等 shifted cone を直和した比較複体。 -/
def complexQuasiIsoSpan (_φ : K ⟶ L) : Complex A := K ⊞ mappingCocone (𝟙 L)

/-- 比較複体から元の始域への射影。 -/
def complexQuasiIsoSpanLeft (φ : K ⟶ L) : complexQuasiIsoSpan φ ⟶ K := biprod.fst

/-- 比較複体から標的への次数ごと全射な射。 -/
def complexQuasiIsoSpanRight (φ : K ⟶ L) : complexQuasiIsoSpan φ ⟶ L :=
  biprod.fst ≫ φ + biprod.snd ≫ mappingCocone.fst (𝟙 L)

/-- 元の始域から比較複体への実切断。 -/
def complexQuasiIsoSpanSection (φ : K ⟶ L) : K ⟶ complexQuasiIsoSpan φ := biprod.inl

/-- 比較の左射影と切断はホモトピー逆である。 -/
def complexQuasiIsoSpanLeftHomotopyEquiv (φ : K ⟶ L) :
    HomotopyEquiv (complexQuasiIsoSpan φ) K where
  hom := complexQuasiIsoSpanLeft φ
  inv := complexQuasiIsoSpanSection φ
  homotopyHomInvId := by
    let h := ((identityCoconeContraction L).compRight
      (biprod.inr : mappingCocone (𝟙 L) ⟶ complexQuasiIsoSpan φ)).compLeft
        (biprod.snd : complexQuasiIsoSpan φ ⟶ mappingCocone (𝟙 L))
    have h' : Homotopy
        (biprod.fst ≫ biprod.inl : complexQuasiIsoSpan φ ⟶ complexQuasiIsoSpan φ)
        (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) := by
      simpa only [Category.comp_id, Category.id_comp, Category.assoc, comp_zero, zero_comp,
        add_zero] using (Homotopy.add (Homotopy.refl
        (biprod.fst ≫ biprod.inl : complexQuasiIsoSpan φ ⟶ complexQuasiIsoSpan φ)) h).symm
    exact h'.trans (Homotopy.ofEq (biprod.total (X := K) (Y := mappingCocone (𝟙 L))))
  homotopyInvHomId := Homotopy.ofEq (by simp [complexQuasiIsoSpanLeft,
    complexQuasiIsoSpanSection])

/-- 比較の切断の後で右射影を取ると、元の鎖写像に厳密に戻る。 -/
lemma complexQuasiIsoSpanSection_right (φ : K ⟶ L) :
    complexQuasiIsoSpanSection φ ≫ complexQuasiIsoSpanRight φ = φ := by
  simp [complexQuasiIsoSpanSection, complexQuasiIsoSpanRight]

/-- 左射影は全次数で全射。 -/
lemma complexQuasiIsoSpanLeft_surjective (φ : K ⟶ L) (i : ℤ) :
    Function.Surjective ((complexQuasiIsoSpanLeft φ).f i) := by
  intro x
  refine ⟨(complexQuasiIsoSpanSection φ).f i x, ?_⟩
  change ((complexQuasiIsoSpanSection φ ≫ complexQuasiIsoSpanLeft φ).f i) x = x
  simp [complexQuasiIsoSpanSection, complexQuasiIsoSpanLeft]

/-- 右射影は全次数で全射。 -/
lemma complexQuasiIsoSpanRight_surjective (φ : K ⟶ L) (i : ℤ) :
    Function.Surjective ((complexQuasiIsoSpanRight φ).f i) := by
  let c := (mappingCocone.inl (𝟙 L)).v i i (add_zero i) ≫
    (biprod.inr : mappingCocone (𝟙 L) ⟶ complexQuasiIsoSpan φ).f i
  have he : (biprod.inr : mappingCocone (𝟙 L) ⟶ complexQuasiIsoSpan φ) ≫
      complexQuasiIsoSpanRight φ = mappingCocone.fst (𝟙 L) := by
    simp [complexQuasiIsoSpanRight]
  have hc : c ≫ (complexQuasiIsoSpanRight φ).f i = 𝟙 _ := by
    rw [Category.assoc, ← HomologicalComplex.comp_f, he]
    exact mappingCocone.inl_v_fst_f (𝟙 L) i
  intro y
  exact ⟨c y, ConcreteCategory.congr_hom hc y⟩

/-- 左射影は常に準同型。 -/
lemma complexQuasiIsoSpanLeft_quasiIso (φ : K ⟶ L) : QuasiIso (complexQuasiIsoSpanLeft φ) :=
  (complexQuasiIsoSpanLeftHomotopyEquiv φ).quasiIso_hom

/-- 元の鎖写像が準同型なら右射影も準同型。 -/
lemma complexQuasiIsoSpanRight_quasiIso (φ : K ⟶ L) [QuasiIso φ] :
    QuasiIso (complexQuasiIsoSpanRight φ) := by
  have : QuasiIso (complexQuasiIsoSpanSection φ) :=
    (complexQuasiIsoSpanLeftHomotopyEquiv φ).quasiIso_inv
  rw [← quasiIso_iff_comp_left (complexQuasiIsoSpanSection φ), complexQuasiIsoSpanSection_right]
  infer_instance

end SerrePositivity.InfinityCategories.Project.DerivedCategories
