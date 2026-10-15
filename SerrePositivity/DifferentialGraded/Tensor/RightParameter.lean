module
public import SerrePositivity.DifferentialGraded.Tensor.Balanced
public import SerrePositivity.DifferentialGraded.Complexes.Closed

/-! # 右に置いたパラメータ複体とbalanced tensorの普遍性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
variable (M : RightModule A D) (N : LeftModule A D)

/-- 各対象のtensorの右にKを置き、二作用の後の▷Kでbalanced条件を課す。 -/
def RightParamFamily (K T : Complex A) :=
  { a : ∀ x : D, objectFamily A D M N x ⊗ K ⟶ T // ∀ x y : D,
    ((rightAction A D M x y ▷ N.obj x) ▷ K) ≫ a x =
      (((α_ (M.obj (op y)) (x ⟶[Complex A] y) (N.obj x)).hom ≫
        M.obj (op y) ◁ leftAction A D N x y) ▷ K) ≫ a y }

/-- 右tensor転置により、右パラメータ族をHom(K,T)値のbalanced族にする。 -/
def curryRightParamFamily {K T : Complex A} (a : RightParamFamily A D M N K T) :
    BalancedFamily A D M N (homComplex A K T) := by
  refine ⟨fun x => curryRight (a.val x), ?_⟩
  intro x y
  have h := congrArg curryRight (a.property x y)
  change curryRight (((rightAction A D M x y ▷ N.obj x) ⊗ₘ 𝟙 K) ≫ a.val x) =
    curryRight ((((α_ (M.obj (op y)) (x ⟶[Complex A] y) (N.obj x)).hom ≫
      M.obj (op y) ◁ leftAction A D N x y) ⊗ₘ 𝟙 K) ≫ a.val y) at h
  rw [curryRight_naturality_source, curryRight_naturality_source] at h
  exact h

variable [Small.{u} D]

/-- 右パラメータを持つbalanced族を(M⊗_D N)⊗Kへ降ろす。 -/
def rightParamDesc {K T : Complex A} (a : RightParamFamily A D M N K T) :
    obj A D M N ⊗ K ⟶ T :=
  uncurryRight (desc A D M N (curryRightParamFamily A D M N a))

@[reassoc (attr := simp)]
lemma ι_rightParamDesc {K T : Complex A} (a : RightParamFamily A D M N K T) (x : D) :
    (ι A D M N x ▷ K) ≫ rightParamDesc A D M N a = a.val x := by
  apply (tensorRightHomEquiv K _ T).injective
  change curryRight ((ι A D M N x ⊗ₘ 𝟙 K) ≫
    uncurryRight (desc A D M N (curryRightParamFamily A D M N a))) = curryRight (a.val x)
  rw [curryRight_naturality_source, curryRight_uncurryRight, ι_desc]
  rfl

lemma rightParam_hom_ext {K T : Complex A} (f g : obj A D M N ⊗ K ⟶ T)
    (h : ∀ x, (ι A D M N x ▷ K) ≫ f = (ι A D M N x ▷ K) ≫ g) : f = g := by
  apply (tensorRightHomEquiv K _ T).injective
  apply hom_ext A D M N
  intro x
  have hx := congrArg curryRight (h x)
  change curryRight ((ι A D M N x ⊗ₘ 𝟙 K) ≫ f) =
    curryRight ((ι A D M N x ⊗ₘ 𝟙 K) ≫ g) at hx
  rw [curryRight_naturality_source, curryRight_naturality_source] at hx
  exact hx

/-- 射を右パラメータ付きの対象ごとの族へ制限する。 -/
def rightParamRestrict {K T : Complex A} (f : obj A D M N ⊗ K ⟶ T) :
    RightParamFamily A D M N K T := by
  refine ⟨fun x => (ι A D M N x ▷ K) ≫ f, ?_⟩
  intro x y
  have h := congrArg (fun t => (t ▷ K) ≫ f) (condition A D M N x y)
  simpa only [comp_whiskerRight, Category.assoc] using h

/-- 右パラメータ付きbalanced tensorの普遍性。 -/
def rightParamHomEquiv (K T : Complex A) :
    (obj A D M N ⊗ K ⟶ T) ≃ RightParamFamily A D M N K T where
  toFun := rightParamRestrict A D M N
  invFun := rightParamDesc A D M N
  left_inv f := by
    apply rightParam_hom_ext A D M N
    intro x
    exact ι_rightParamDesc A D M N (rightParamRestrict A D M N f) x
  right_inv a := by
    apply Subtype.ext
    funext x
    exact ι_rightParamDesc A D M N a x

end SerrePositivity.DifferentialGraded.BalancedTensor
