module
public import SerrePositivity.DifferentialGraded.Tensor.Actions
public import SerrePositivity.DifferentialGraded.Module.Colimits
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-! # 多対象dg加群のbalanced tensor

二作用を直和からの二つの射として保持し、その余等化子を使う。
対象の添字はu-small。射の普遍性は全chain mapのbalanced族によって述べる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Limits MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (M : RightModule A D) (N : LeftModule A D)

abbrev objectFamily (x : D) : Complex A := M.obj (op x) ⊗ N.obj x
abbrev relationFamily (xy : D × D) : Complex A :=
  (M.obj (op xy.2) ⊗ (xy.1 ⟶[Complex A] xy.2)) ⊗ N.obj xy.1

abbrev generators : Complex A := ∐ objectFamily A D M N
abbrev relations : Complex A := ∐ relationFamily A D M N

/-- 右作用から得られる関係射。 -/
def relationLeft : relations A D M N ⟶ generators A D M N :=
  Sigma.desc (fun xy => (rightAction A D M xy.1 xy.2 ▷ N.obj xy.1) ≫
    Sigma.ι (objectFamily A D M N) xy.1)

/-- 左作用から得られる関係射。 -/
def relationRight : relations A D M N ⟶ generators A D M N :=
  Sigma.desc (fun xy => (α_ (M.obj (op xy.2)) (xy.1 ⟶[Complex A] xy.2) (N.obj xy.1)).hom ≫
    M.obj (op xy.2) ◁ leftAction A D N xy.1 xy.2 ≫ Sigma.ι (objectFamily A D M N) xy.2)

/-- 多対象balanced tensorの複体。 -/
def obj : Complex A := coequalizer (relationLeft A D M N) (relationRight A D M N)

def projection : generators A D M N ⟶ obj A D M N := coequalizer.π _ _

def ι (x : D) : objectFamily A D M N x ⟶ obj A D M N :=
  Sigma.ι (objectFamily A D M N) x ≫ projection A D M N

lemma condition (x y : D) :
    (rightAction A D M x y ▷ N.obj x) ≫ ι A D M N x =
      (α_ (M.obj (op y)) (x ⟶[Complex A] y) (N.obj x)).hom ≫
        M.obj (op y) ◁ leftAction A D N x y ≫ ι A D M N y := by
  have h := congrArg (fun f => Sigma.ι (relationFamily A D M N) (x, y) ≫ f)
    (coequalizer.condition (relationLeft A D M N) (relationRight A D M N))
  simpa only [relationLeft, relationRight, Sigma.ι_comp_desc_assoc, Category.assoc,
    ι, projection] using h

/-- 指定複体へのbalancedなchain map族。 -/
def BalancedFamily (T : Complex A) :=
  { a : ∀ x : D, objectFamily A D M N x ⟶ T // ∀ x y : D,
    (rightAction A D M x y ▷ N.obj x) ≫ a x =
      (α_ (M.obj (op y)) (x ⟶[Complex A] y) (N.obj x)).hom ≫
        M.obj (op y) ◁ leftAction A D N x y ≫ a y }

/-- balanced族をtensor全体へ降ろす。 -/
def desc {T : Complex A} (a : BalancedFamily A D M N T) : obj A D M N ⟶ T :=
  coequalizer.desc (Sigma.desc a.val) (by
    apply Sigma.hom_ext
    intro xy
    simp only [relationLeft, relationRight, Sigma.ι_comp_desc_assoc, Category.assoc,
      Sigma.ι_comp_desc]
    exact a.property xy.1 xy.2)

@[reassoc (attr := simp)]
lemma ι_desc {T : Complex A} (a : BalancedFamily A D M N T) (x : D) :
    ι A D M N x ≫ desc A D M N a = a.val x := by
  simp only [ι, desc, projection, Category.assoc, coequalizer.π_desc, Sigma.ι_comp_desc]

lemma hom_ext {T : Complex A} (f g : obj A D M N ⟶ T)
    (h : ∀ x, ι A D M N x ≫ f = ι A D M N x ≫ g) : f = g := by
  apply coequalizer.hom_ext
  apply Sigma.hom_ext
  intro x
  exact h x

/-- balanced族との自然な普遍性。自然性の式は後続で公開する。 -/
def homEquiv (T : Complex A) : (obj A D M N ⟶ T) ≃ BalancedFamily A D M N T where
  toFun f := ⟨fun x => ι A D M N x ≫ f, fun x y => by
    simpa only [Category.assoc] using congrArg (fun a => a ≫ f) (condition A D M N x y)⟩
  invFun := desc A D M N
  left_inv f := by
    apply hom_ext
    intro x
    exact ι_desc A D M N _ x
  right_inv a := by
    apply Subtype.ext
    funext x
    exact ι_desc A D M N a x

/-- balanced族の終域での後合成。 -/
def postcompose {T T' : Complex A} (a : BalancedFamily A D M N T) (f : T ⟶ T') :
    BalancedFamily A D M N T' :=
  ⟨fun x => a.val x ≫ f, fun x y => by
    simpa only [Category.assoc] using congrArg (fun t => t ≫ f) (a.property x y)⟩

lemma homEquiv_naturality {T T' : Complex A} (f : obj A D M N ⟶ T) (g : T ⟶ T') :
    homEquiv A D M N T' (f ≫ g) = postcompose A D M N (homEquiv A D M N T f) g := by
  apply Subtype.ext
  funext x
  exact (Category.assoc _ _ _).symm

lemma desc_postcompose {T T' : Complex A} (a : BalancedFamily A D M N T) (f : T ⟶ T') :
    desc A D M N (postcompose A D M N a f) = desc A D M N a ≫ f := by
  apply hom_ext
  intro x
  simp only [ι_desc, ι_desc_assoc]
  rfl

end SerrePositivity.DifferentialGraded.BalancedTensor
