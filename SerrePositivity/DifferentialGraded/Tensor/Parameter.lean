module
public import SerrePositivity.DifferentialGraded.Tensor.Balanced
public import SerrePositivity.DifferentialGraded.Complexes.Closed

/-! # パラメータ付きbalanced族の降下と普遍性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Limits MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (M : RightModule A D) (N : LeftModule A D)

/-- Kを左に置くbalancedな全chain map族。 -/
def ParamFamily (K T : Complex A) :=
  { a : ∀ x : D, K ⊗ objectFamily A D M N x ⟶ T // ∀ x y : D,
    (K ◁ (rightAction A D M x y ▷ N.obj x)) ≫ a x =
      (K ◁ ((α_ (M.obj (op y)) (x ⟶[Complex A] y) (N.obj x)).hom ≫
        M.obj (op y) ◁ leftAction A D N x y)) ≫ a y }

/-- 登録済みの左tensor–Hom随伴でパラメータを終域へ移す。 -/
def curryParamFamily {K T : Complex A} (a : ParamFamily A D M N K T) :
    BalancedFamily A D M N (homComplex A K T) := by
  refine ⟨fun x => tensorHomEquiv K _ T (a.val x), ?_⟩
  intro x y
  change (rightAction A D M x y ▷ N.obj x) ≫ tensorHomEquiv K _ T (a.val x) =
    ((α_ (M.obj (op y)) (x ⟶[Complex A] y) (N.obj x)).hom ≫
      M.obj (op y) ◁ leftAction A D N x y) ≫ tensorHomEquiv K _ T (a.val y)
  rw [← tensorHomEquiv_naturality_source, ← tensorHomEquiv_naturality_source]
  exact congrArg (tensorHomEquiv K _ T) (a.property x y)

/-- パラメータ付きbalanced族をK⊗(M⊗_D N)へ降ろす。 -/
def paramDesc {K T : Complex A} (a : ParamFamily A D M N K T) :
    K ⊗ obj A D M N ⟶ T :=
  (tensorHomEquiv K _ T).symm (desc A D M N (curryParamFamily A D M N a))

@[reassoc (attr := simp)]
lemma ι_paramDesc {K T : Complex A} (a : ParamFamily A D M N K T) (x : D) :
    (K ◁ ι A D M N x) ≫ paramDesc A D M N a = a.val x := by
  apply (tensorHomEquiv K _ T).injective
  rw [tensorHomEquiv_naturality_source]
  simp only [paramDesc, Equiv.apply_symm_apply, ι_desc, curryParamFamily]

/-- Kとのtensor後も、対象ごとの包含で射を判定できる。 -/
lemma param_hom_ext {K T : Complex A} (f g : K ⊗ obj A D M N ⟶ T)
    (h : ∀ x, (K ◁ ι A D M N x) ≫ f = (K ◁ ι A D M N x) ≫ g) : f = g := by
  apply (tensorHomEquiv K _ T).injective
  apply hom_ext
  intro x
  rw [← tensorHomEquiv_naturality_source, ← tensorHomEquiv_naturality_source]
  exact congrArg (tensorHomEquiv K _ T) (h x)

/-- 射を各対象のパラメータ付きbalanced族へ制限する。 -/
def paramRestrict {K T : Complex A} (f : K ⊗ obj A D M N ⟶ T) :
    ParamFamily A D M N K T := by
  refine ⟨fun x => (K ◁ ι A D M N x) ≫ f, ?_⟩
  intro x y
  have h := congrArg (fun t => (K ◁ t) ≫ f) (condition A D M N x y)
  simpa only [MonoidalCategory.whiskerLeft_comp, Category.assoc] using h

/-- パラメータ付きbalanced tensorの普遍性。 -/
def paramHomEquiv (K T : Complex A) :
    (K ⊗ obj A D M N ⟶ T) ≃ ParamFamily A D M N K T where
  toFun := paramRestrict A D M N
  invFun := paramDesc A D M N
  left_inv f := by
    apply param_hom_ext
    intro x
    exact ι_paramDesc A D M N (paramRestrict A D M N f) x
  right_inv a := by
    apply Subtype.ext
    funext x
    exact ι_paramDesc A D M N a x

/-- パラメータ付きbalanced族の終域での後合成。 -/
def paramPostcompose {K T T' : Complex A} (a : ParamFamily A D M N K T) (f : T ⟶ T') :
    ParamFamily A D M N K T' :=
  ⟨fun x => a.val x ≫ f, fun x y => by
    simpa only [Category.assoc] using congrArg (fun t => t ≫ f) (a.property x y)⟩

lemma paramDesc_postcompose {K T T' : Complex A} (a : ParamFamily A D M N K T) (f : T ⟶ T') :
    paramDesc A D M N (paramPostcompose A D M N a f) = paramDesc A D M N a ≫ f := by
  apply param_hom_ext
  intro x
  simp only [ι_paramDesc, ι_paramDesc_assoc, paramPostcompose]

/-- パラメータ複体の射による引戻し。 -/
def paramPrecompose {K K' T : Complex A} (g : K' ⟶ K) (a : ParamFamily A D M N K T) :
    ParamFamily A D M N K' T := by
  refine ⟨fun x => (g ▷ objectFamily A D M N x) ≫ a.val x, ?_⟩
  intro x y
  rw [← Category.assoc, whisker_exchange, Category.assoc, a.property x y,
    ← Category.assoc, ← whisker_exchange, Category.assoc]

lemma paramDesc_precompose {K K' T : Complex A} (g : K' ⟶ K)
    (a : ParamFamily A D M N K T) :
    paramDesc A D M N (paramPrecompose A D M N g a) =
      (g ▷ obj A D M N) ≫ paramDesc A D M N a := by
  apply param_hom_ext
  intro x
  simp only [ι_paramDesc, paramPrecompose]
  rw [← Category.assoc, whisker_exchange, Category.assoc, ι_paramDesc]

/-- 降下射を主Hom複体に値を持つパラメータ付き射として束ねる。 -/
def paramHomMap {K T : Complex A} (a : ParamFamily A D M N K T) :
    K ⟶ homComplex A (obj A D M N) T := curryRight (paramDesc A D M N a)

@[reassoc]
lemma paramHomMap_ι {K T : Complex A} (a : ParamFamily A D M N K T) (x : D) :
    paramHomMap A D M N a ≫ homPrecompose (ι A D M N x) T = curryRight (a.val x) := by
  rw [paramHomMap, ← curryRight_naturality_domain]
  change curryRight ((K ◁ ι A D M N x) ≫ paramDesc A D M N a) = _
  rw [ι_paramDesc]

end SerrePositivity.DifferentialGraded.BalancedTensor
