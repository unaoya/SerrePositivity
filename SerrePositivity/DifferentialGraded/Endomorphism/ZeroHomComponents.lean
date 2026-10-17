module
public import SerrePositivity.DifferentialGraded.Endomorphism.GradedSplitRelations

/-! # 零次数Hom要素の次数付き加群射としての成分 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def zeroHomComponent {M N : RightModule A D} (a : (moduleHom A D M N).X 0)
    (x : D) (i : ℤ) : (M.obj (op x)).X i ⟶ (N.obj (op x)).X i :=
  ((moduleHomπ A D M N x).f 0 a).v i i (add_zero i)

lemma zeroHomComponent_forward {M N P : RightModule A D}
    (a : (moduleHom A D M N).X 0) (b : (moduleHom A D N P).X 0) (x : D) (i : ℤ) :
    zeroHomComponent A D (forward A (D := RightModule A D) a b (zero_add 0)) x i =
      zeroHomComponent A D a x i ≫ zeroHomComponent A D b x i := by
  unfold zeroHomComponent
  rw [moduleHomForward_π]
  simp only [zero_mul, Int.negOnePow_zero, one_smul]
  exact Cochain.comp_v _ _ _ i i i (add_zero i) (add_zero i)

@[simp]
lemma zeroHomComponent_unit (M : RightModule A D) (x : D) (i : ℤ) :
    zeroHomComponent A D (unitElement A M).val x i = 𝟙 _ := by
  unfold zeroHomComponent
  rw [yoneda_moduleUnit_π]
  rfl

@[simp]
lemma zeroHomComponent_closed {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) (i : ℤ) :
    zeroHomComponent A D (endomorphismClosedElement A D f) x i =
      ((moduleEvaluation A D x).map f).f i := by
  unfold zeroHomComponent
  rw [endomorphismClosedElement_π]
  rfl

@[simp]
lemma zeroHomComponent_zero (M N : RightModule A D) (x : D) (i : ℤ) :
    zeroHomComponent A D (0 : (moduleHom A D M N).X 0) x i = 0 := by
  simp [zeroHomComponent]

@[simp]
lemma zeroHomComponent_add {M N : RightModule A D} (a b : (moduleHom A D M N).X 0)
    (x : D) (i : ℤ) :
    zeroHomComponent A D (a + b) x i = zeroHomComponent A D a x i + zeroHomComponent A D b x i := by
  simp [zeroHomComponent]

lemma zeroHomComponent_naturality {M N : RightModule A D} (a : (moduleHom A D M N).X 0)
    (x y : D) (p i j : ℤ) (hij : i + p = j) (f : GradedHom A (op x) (op y) p) :
    ((M.map (op x) (op y)).f p f).v i j hij ≫ zeroHomComponent A D a y j =
      zeroHomComponent A D a x i ≫ ((N.map (op x) (op y)).f p f).v i j hij := by
  have h := congrArg (fun c => c.v i j (by omega))
    (moduleHomElement_naturality A D 0 a (op x) (op y) p f)
  simp only [zero_mul, Int.negOnePow_zero, one_smul] at h
  rw [Cochain.comp_v _ _ _ i j j hij (add_zero j),
    Cochain.comp_v _ _ _ i i j (add_zero i) hij] at h
  exact h

end SerrePositivity.DifferentialGraded
