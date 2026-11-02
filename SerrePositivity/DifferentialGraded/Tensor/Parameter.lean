module

public import SerrePositivity.DifferentialGraded.Module.ActionLimits
public import SerrePositivity.DifferentialGraded.Module.Basic

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import SerrePositivity.DifferentialGraded.Module.Graded
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
public import SerrePositivity.DifferentialGraded.Module.TensorFree


public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying

public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct


/-!
# Tensor.Parameter

## 概要
14 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## Actions（旧 SerrePositivity/DifferentialGraded/Tensor/Actions.lean） -/

/-! # balanced tensorの二つの作用射と成分の符号 -/

@[expose] public section Actions
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- M(y)⊗D(x,y)からM(x)への右作用。 -/
def rightAction (M : RightModule A D) (x y : D) :
    M.obj (op y) ⊗ (x ⟶[Complex A] y) ⟶ M.obj (op x) :=
  (signedSwap (M.obj (op y)) (x ⟶[Complex A] y)).hom ≫
    moduleActionChain A M (op y) (op x)

/-- D(x,y)⊗N(x)からN(y)への左作用。 -/
def leftAction (N : LeftModule A D) (x y : D) :
    (x ⟶[Complex A] y) ⊗ N.obj x ⟶ N.obj y := uncurryRight (N.map x y)

/-- 右作用ではHomと加群値の順を交換する符号を保持する。 -/
lemma rightAction_apply (M : RightModule A D) (x y : D) (r p n : ℤ) (hn : r + p = n)
    (m : (M.obj (op y)).X r) (f : GradedHom A x y p) :
    (rightAction A D M x y).f n
      (ιTensorObj (M.obj (op y)) (x ⟶[Complex A] y) r p n hn (m ⊗ₜ[A] f)) =
      (r * p).negOnePow • moduleAction A M f m hn := by
  change (uncurryRight (M.map (op y) (op x))).f n
    ((signedSwap (M.obj (op y)) (x ⟶[Complex A] y)).hom.f n
      (ιTensorObj (M.obj (op y)) (x ⟶[Complex A] y) r p n hn (m ⊗ₜ[A] f))) = _
  rw [signedSwap_apply]
  simp only [Units.smul_def, map_zsmul]
  exact congrArg (fun t : (M.obj (op x)).X n => ((r * p).negOnePow : ℤ) • t)
    (uncurryRight_apply (M.map (op y) (op x)) p r n (by omega) f m)

lemma leftAction_apply (N : LeftModule A D) (x y : D) (p r n : ℤ) (hn : p + r = n)
    (f : GradedHom A x y p) (m : (N.obj x).X r) :
    (leftAction A D N x y).f n
      (ιTensorObj (x ⟶[Complex A] y) (N.obj x) p r n hn (f ⊗ₜ[A] m)) =
      SerrePositivity.DifferentialGraded.leftAction A N f m (by omega) :=
  uncurryRight_apply (N.map x y) p r n hn f m

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end Actions

/-! ## Balanced（旧 SerrePositivity/DifferentialGraded/Tensor/Balanced.lean） -/

/-! # 多対象dg加群のbalanced tensor

二作用を直和からの二つの射として保持し、その余等化子を使う。
対象の添字はu-small。射の普遍性は全chain mapのbalanced族によって述べる。
-/

@[expose] public section Balanced
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end Balanced

/-! ## Maps（旧 SerrePositivity/DifferentialGraded/Tensor/Maps.lean） -/

/-! # balanced tensorの両変数の作用可換なchain map族 -/

@[expose] public section Maps
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Limits MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M M' : RightModule A D} {N N' : LeftModule A D}

/-- 対象の直和上の両変数map。 -/
def generatorMap (f : ∀ x, M.obj (op x) ⟶ M'.obj (op x))
    (g : ∀ x, N.obj x ⟶ N'.obj x) : generators A D M N ⟶ generators A D M' N' :=
  Limits.Sigma.map (fun x : D => f x ⊗ₘ g x)

/-- 関係の直和上の両変数map。 -/
def relationMap (f : ∀ x, M.obj (op x) ⟶ M'.obj (op x))
    (g : ∀ x, N.obj x ⟶ N'.obj x) : relations A D M N ⟶ relations A D M' N' :=
  Limits.Sigma.map (fun xy : D × D => (f xy.2 ⊗ₘ 𝟙 (xy.1 ⟶[Complex A] xy.2)) ⊗ₘ g xy.1)

lemma relationLeft_naturality
    (f : ∀ x, M.obj (op x) ⟶ M'.obj (op x)) (g : ∀ x, N.obj x ⟶ N'.obj x)
    (hf : ∀ x y, rightAction A D M x y ≫ f x =
      (f y ⊗ₘ 𝟙 (x ⟶[Complex A] y)) ≫ rightAction A D M' x y) :
    relationMap A D f g ≫ relationLeft A D M' N' =
      relationLeft A D M N ≫ generatorMap A D f g := by
  apply Sigma.hom_ext
  intro xy
  simp only [relationMap, relationLeft, generatorMap, Sigma.ι_map_assoc,
    Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, Category.assoc, Sigma.ι_map]
  have h : ((f xy.2 ⊗ₘ 𝟙 (xy.1 ⟶[Complex A] xy.2)) ⊗ₘ g xy.1) ≫
      (rightAction A D M' xy.1 xy.2 ⊗ₘ 𝟙 (N'.obj xy.1)) =
    (rightAction A D M xy.1 xy.2 ⊗ₘ 𝟙 (N.obj xy.1)) ≫ (f xy.1 ⊗ₘ g xy.1) := by
    simp only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    rw [hf]
  simpa only [tensorHom_id, Category.assoc] using
    congrArg (fun h => h ≫ Sigma.ι (objectFamily A D M' N') xy.1) h

lemma relationRight_naturality
    (f : ∀ x, M.obj (op x) ⟶ M'.obj (op x)) (g : ∀ x, N.obj x ⟶ N'.obj x)
    (hg : ∀ x y, leftAction A D N x y ≫ g y =
      (𝟙 (x ⟶[Complex A] y) ⊗ₘ g x) ≫ leftAction A D N' x y) :
    relationMap A D f g ≫ relationRight A D M' N' =
      relationRight A D M N ≫ generatorMap A D f g := by
  apply Sigma.hom_ext
  intro xy
  simp only [relationMap, relationRight, generatorMap, Sigma.ι_map_assoc,
    Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, Category.assoc, Sigma.ι_map]
  have h : ((f xy.2 ⊗ₘ 𝟙 (xy.1 ⟶[Complex A] xy.2)) ⊗ₘ g xy.1) ≫
      (α_ (M'.obj (op xy.2)) (xy.1 ⟶[Complex A] xy.2) (N'.obj xy.1)).hom ≫
        (𝟙 (M'.obj (op xy.2)) ⊗ₘ leftAction A D N' xy.1 xy.2) =
    (α_ (M.obj (op xy.2)) (xy.1 ⟶[Complex A] xy.2) (N.obj xy.1)).hom ≫
      (𝟙 (M.obj (op xy.2)) ⊗ₘ leftAction A D N xy.1 xy.2) ≫ (f xy.2 ⊗ₘ g xy.2) := by
    rw [associator_naturality_assoc]
    simp only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    rw [hg]
  simpa only [id_tensorHom, Category.assoc] using
    congrArg (fun h => h ≫ Sigma.ι (objectFamily A D M' N') xy.2) h

/-- 作用と可換な両変数のchain map族をbalanced tensorへ降ろす。 -/
def mapOfFamilies
    (f : ∀ x, M.obj (op x) ⟶ M'.obj (op x)) (g : ∀ x, N.obj x ⟶ N'.obj x)
    (hf : ∀ x y, rightAction A D M x y ≫ f x =
      (f y ⊗ₘ 𝟙 (x ⟶[Complex A] y)) ≫ rightAction A D M' x y)
    (hg : ∀ x y, leftAction A D N x y ≫ g y =
      (𝟙 (x ⟶[Complex A] y) ⊗ₘ g x) ≫ leftAction A D N' x y) :
    obj A D M N ⟶ obj A D M' N' :=
  coequalizer.desc (generatorMap A D f g ≫ projection A D M' N') (by
    rw [← Category.assoc, ← relationLeft_naturality A D f g hf, Category.assoc,
      projection, coequalizer.condition, ← Category.assoc,
      relationRight_naturality A D f g hg, Category.assoc])

@[reassoc (attr := simp)]
lemma ι_mapOfFamilies
    (f : ∀ x, M.obj (op x) ⟶ M'.obj (op x)) (g : ∀ x, N.obj x ⟶ N'.obj x) (hf hg) (x : D) :
    ι A D M N x ≫ mapOfFamilies A D f g hf hg = (f x ⊗ₘ g x) ≫ ι A D M' N' x := by
  simp only [ι, mapOfFamilies, projection, Category.assoc, coequalizer.π_desc,
    generatorMap, Sigma.ι_map_assoc]

lemma mapOfFamilies_id (M : RightModule A D) (N : LeftModule A D) (hf hg) :
    mapOfFamilies A D (fun x => 𝟙 (M.obj (op x))) (fun x => 𝟙 (N.obj x)) hf hg =
      𝟙 (obj A D M N) := by
  apply hom_ext
  intro x
  simp

variable {M'' : RightModule A D} {N'' : LeftModule A D}
lemma mapOfFamilies_comp
    (f : ∀ x, M.obj (op x) ⟶ M'.obj (op x)) (g : ∀ x, N.obj x ⟶ N'.obj x)
    (f' : ∀ x, M'.obj (op x) ⟶ M''.obj (op x)) (g' : ∀ x, N'.obj x ⟶ N''.obj x)
    (hf hg hf' hg' hff hgg) :
    mapOfFamilies A D f g hf hg ≫ mapOfFamilies A D f' g' hf' hg' =
      mapOfFamilies A D (fun x => f x ≫ f' x) (fun x => g x ≫ g' x) hff hgg := by
  apply hom_ext
  intro x
  rw [ι_mapOfFamilies_assoc, ι_mapOfFamilies, ι_mapOfFamilies]
  simp only [tensorHom_comp_tensorHom_assoc]

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end Maps

/-! ## Functor（旧 SerrePositivity/DifferentialGraded/Tensor/Functor.lean） -/

/-! # 右dg加群・左dg加群上のbalanced tensor双関手 -/

@[expose] public section Functor
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Limits MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma rightAction_morphism {M M' : ModuleCategory A D} (f : M ⟶ M') (x y : D) :
    rightAction A D (ForgetEnrichment.to (Complex A) M) x y ≫ (moduleEvaluation A D x).map f =
      ((moduleEvaluation A D y).map f ⊗ₘ 𝟙 (x ⟶[Complex A] y)) ≫
        rightAction A D (ForgetEnrichment.to (Complex A) M') x y := by
  unfold rightAction
  rw [Category.assoc, moduleMorphism_action_chain]
  let fy : (ForgetEnrichment.to (Complex A) M).obj (op y) ⟶
      (ForgetEnrichment.to (Complex A) M').obj (op y) := (moduleEvaluation A D y).map f
  have h := signedSwap_naturality fy (𝟙 (x ⟶[Complex A] y))
  change (signedSwap ((ForgetEnrichment.to (Complex A) M).obj (op y))
      (x ⟶[Complex A] y)).hom ≫ (𝟙 (x ⟶[Complex A] y) ⊗ₘ fy) ≫
        moduleActionChain A (ForgetEnrichment.to (Complex A) M') (op y) (op x) =
    (fy ⊗ₘ 𝟙 (x ⟶[Complex A] y)) ≫
      (signedSwap ((ForgetEnrichment.to (Complex A) M').obj (op y))
        (x ⟶[Complex A] y)).hom ≫
          moduleActionChain A (ForgetEnrichment.to (Complex A) M') (op y) (op x)
  simpa only [Category.assoc] using congrArg (fun t => t ≫
    moduleActionChain A (ForgetEnrichment.to (Complex A) M') (op y) (op x)) h.symm

lemma leftAction_morphism {N N' : LeftModuleCategory A D} (g : N ⟶ N') (x y : D) :
    leftAction A D (ForgetEnrichment.to (Complex A) N) x y ≫ (leftModuleEvaluation A D y).map g =
      (𝟙 (x ⟶[Complex A] y) ⊗ₘ (leftModuleEvaluation A D x).map g) ≫
        leftAction A D (ForgetEnrichment.to (Complex A) N') x y :=
  leftModuleMorphism_action_chain A D g x y

/-- 閉零加群圏の両方の射に関するbalanced tensorのmap。 -/
def map {M M' : ModuleCategory A D} {N N' : LeftModuleCategory A D} (f : M ⟶ M') (g : N ⟶ N') :
    obj A D (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N) ⟶
      obj A D (ForgetEnrichment.to (Complex A) M') (ForgetEnrichment.to (Complex A) N') :=
  mapOfFamilies A D (fun x => (moduleEvaluation A D x).map f)
    (fun x => (leftModuleEvaluation A D x).map g)
    (rightAction_morphism A D f) (leftAction_morphism A D g)

@[reassoc (attr := simp)]
lemma ι_map {M M' : ModuleCategory A D} {N N' : LeftModuleCategory A D}
    (f : M ⟶ M') (g : N ⟶ N') (x : D) :
    ι A D (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N) x ≫ map A D f g =
      ((moduleEvaluation A D x).map f ⊗ₘ (leftModuleEvaluation A D x).map g) ≫
        ι A D (ForgetEnrichment.to (Complex A) M') (ForgetEnrichment.to (Complex A) N') x :=
  ι_mapOfFamilies A D _ _ _ _ x

lemma map_id (M : ModuleCategory A D) (N : LeftModuleCategory A D) :
    map A D (𝟙 M) (𝟙 N) = 𝟙 _ := by
  apply hom_ext
  intro x
  simp

lemma map_comp {M M' M'' : ModuleCategory A D} {N N' N'' : LeftModuleCategory A D}
    (f : M ⟶ M') (f' : M' ⟶ M'') (g : N ⟶ N') (g' : N' ⟶ N'') :
    map A D (f ≫ f') (g ≫ g') = map A D f g ≫ map A D f' g' := by
  apply hom_ext
  intro x
  simp only [ι_map, ι_map_assoc, CategoryTheory.Functor.map_comp, tensorHom_comp_tensorHom_assoc]

/-- 両変数で共変な、実際の閉零加群圏の積からの関手。 -/
def functor : ModuleCategory A D × LeftModuleCategory A D ⥤ Complex A where
  obj MN := obj A D (ForgetEnrichment.to (Complex A) MN.1) (ForgetEnrichment.to (Complex A) MN.2)
  map fg := map A D fg.1 fg.2
  map_id MN := map_id A D MN.1 MN.2
  map_comp fg gh := map_comp A D fg.1 gh.1 fg.2 gh.2

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end Functor

/-! ## Elements（旧 SerrePositivity/DifferentialGraded/Tensor/Elements.lean） -/

/-! # balanced tensorの斉次要素・作用関係・両変数map -/

@[expose] public section Elements
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Limits Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 対象xでの純粋斉次tensorの像。 -/
def element (M : RightModule A D) (N : LeftModule A D) (x : D) {r s n : ℤ}
    (m : (M.obj (op x)).X r) (t : (N.obj x).X s) (hn : r + s = n) : (obj A D M N).X n :=
  (ι A D M N x).f n (ιTensorObj (M.obj (op x)) (N.obj x) r s n hn (m ⊗ₜ[A] t))

/-- balanced関係は右作用のKoszul符号を含む。 -/
lemma element_balanced (M : RightModule A D) (N : LeftModule A D) (x y : D)
    {a p b n : ℤ} (m : (M.obj (op y)).X a) (f : GradedHom A x y p)
    (t : (N.obj x).X b) (hn : a + p + b = n) :
    (a * p).negOnePow • element A D M N x
      (moduleAction A M (x := op y) (y := op x) f m rfl) t hn =
    element A D M N y m
      (SerrePositivity.DifferentialGraded.leftAction A N (x := x) (y := y)
        (n := p + b) f t (by omega)) (by omega) := by
  have h := congrArg (fun k => k.f n
    (ιTensorObj (M.obj (op y) ⊗ (x ⟶[Complex A] y)) (N.obj x) (a + p) b n hn
      (ιTensorObj (M.obj (op y)) (x ⟶[Complex A] y) a p (a + p) rfl (m ⊗ₜ[A] f) ⊗ₜ[A] t)))
    (condition A D M N x y)
  change (ι A D M N x).f n
    ((rightAction A D M x y ▷ N.obj x).f n
      (ιTensorObj (M.obj (op y) ⊗ (x ⟶[Complex A] y)) (N.obj x) (a + p) b n hn
        (ιTensorObj (M.obj (op y)) (x ⟶[Complex A] y) a p (a + p) rfl (m ⊗ₜ[A] f) ⊗ₜ[A] t))) =
    (ι A D M N y).f n
      ((M.obj (op y) ◁ leftAction A D N x y).f n
        ((α_ (M.obj (op y)) (x ⟶[Complex A] y) (N.obj x)).hom.f n
          (ιTensorObj (M.obj (op y) ⊗ (x ⟶[Complex A] y)) (N.obj x) (a + p) b n hn
            (ιTensorObj (M.obj (op y)) (x ⟶[Complex A] y) a p (a + p) rfl
              (m ⊗ₜ[A] f) ⊗ₜ[A] t)))) at h
  rw [whiskerRight_apply, rightAction_apply, associator_apply,
    whiskerLeft_apply, leftAction_apply] at h
  simpa only [element, Units.smul_def, ← TensorProduct.smul_tmul', map_zsmul] using h

lemma map_element {M M' : ModuleCategory A D} {N N' : LeftModuleCategory A D}
    (f : M ⟶ M') (g : N ⟶ N') (x : D) {r s n : ℤ}
    (m : ((ForgetEnrichment.to (Complex A) M).obj (op x)).X r)
    (t : ((ForgetEnrichment.to (Complex A) N).obj x).X s) (hn : r + s = n) :
    (map A D f g).f n
      (element A D (ForgetEnrichment.to (Complex A) M)
        (ForgetEnrichment.to (Complex A) N) x m t hn) =
    element A D (ForgetEnrichment.to (Complex A) M') (ForgetEnrichment.to (Complex A) N') x
      (((moduleEvaluation A D x).map f).f r m) (((leftModuleEvaluation A D x).map g).f s t) hn := by
  have h := congrArg (fun k => k.f n
    (ιTensorObj ((ForgetEnrichment.to (Complex A) M).obj (op x))
      ((ForgetEnrichment.to (Complex A) N).obj x) r s n hn (m ⊗ₜ[A] t))) (ι_map A D f g x)
  change (map A D f g).f n (element A D _ _ x m t hn) =
    (ι A D _ _ x).f n
      ((((moduleEvaluation A D x).map f) ⊗ₘ ((leftModuleEvaluation A D x).map g)).f n
        (ιTensorObj ((ForgetEnrichment.to (Complex A) M).obj (op x))
          ((ForgetEnrichment.to (Complex A) N).obj x) r s n hn (m ⊗ₜ[A] t))) at h
  let fx : (ForgetEnrichment.to (Complex A) M).obj (op x) ⟶
      (ForgetEnrichment.to (Complex A) M').obj (op x) := (moduleEvaluation A D x).map f
  let gx : (ForgetEnrichment.to (Complex A) N).obj x ⟶
      (ForgetEnrichment.to (Complex A) N').obj x := (leftModuleEvaluation A D x).map g
  have he := tensorMap_apply fx gx r s n hn m t
  exact h.trans (congrArg (fun z => (ι A D _ _ x).f n z) he)

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end Elements

/-! ## Ring（旧 SerrePositivity/DifferentialGraded/Tensor/Ring.lean） -/

/-! # 一対象環上のbalanced tensorと通常の非有界tensorの比較 -/

@[expose] public section Ring
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Limits MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A]

lemma ring_rightAction (M : RightModule A PUnit.{1}) (x : PUnit.{1}) :
    rightAction A PUnit.{1} M x x = (ρ_ (M.obj (op x))).hom := by
  change (signedSwap (M.obj (op x)) (𝟙_ (Complex A))).hom ≫
    uncurryRight (M.map (op x) (op x)) = _
  rw [ringModule_map, uncurryRight_identity]
  exact braiding_leftUnitor _

lemma ring_leftAction (N : LeftModule A PUnit.{1}) (x : PUnit.{1}) :
    leftAction A PUnit.{1} N x x = (λ_ (N.obj x)).hom := by
  unfold leftAction
  rw [ringLeftModule_map, uncurryRight_identity]

/-- 一対象環では恒等tensor写像の族がbalancedである。 -/
def ringFamily (M : RightModule A PUnit.{1}) (N : LeftModule A PUnit.{1}) :
    BalancedFamily A PUnit.{1} M N (M.obj (op PUnit.unit) ⊗ N.obj PUnit.unit) := by
  refine ⟨fun x => by cases x; exact 𝟙 _, ?_⟩
  intro x y
  cases x
  cases y
  simp only [Category.comp_id, ring_rightAction, ring_leftAction]
  monoidal_coherence

/-- 任意の一対象dg加群のbalanced tensorは値の通常tensorに同型。 -/
def ringIso (M : RightModule A PUnit.{1}) (N : LeftModule A PUnit.{1}) :
    obj A PUnit.{1} M N ≅ M.obj (op PUnit.unit) ⊗ N.obj PUnit.unit where
  hom := desc A PUnit.{1} M N (ringFamily A M N)
  inv := ι A PUnit.{1} M N PUnit.unit
  hom_inv_id := by
    apply hom_ext
    intro x
    cases x
    rw [ι_desc_assoc]
    simp only [ringFamily, Category.id_comp, Category.comp_id]
  inv_hom_id := ι_desc A PUnit.{1} M N (ringFamily A M N) PUnit.unit

@[reassoc (attr := simp)]
lemma ι_ringIso_hom (M : RightModule A PUnit.{1}) (N : LeftModule A PUnit.{1}) :
    ι A PUnit.{1} M N PUnit.unit ≫ (ringIso A M N).hom = 𝟙 _ :=
  ι_desc A PUnit.{1} M N (ringFamily A M N) PUnit.unit

lemma ringIso_hom_element (M : RightModule A PUnit.{1}) (N : LeftModule A PUnit.{1})
    {r s n : ℤ} (m : (M.obj (op PUnit.unit)).X r) (v : (N.obj PUnit.unit).X s)
    (hn : r + s = n) :
    (ringIso A M N).hom.f n (element A PUnit.{1} M N PUnit.unit m v hn) =
      ιTensorObj (M.obj (op PUnit.unit)) (N.obj PUnit.unit) r s n hn (m ⊗ₜ[A] v) := by
  exact congrArg (fun f => f.f n
    (ιTensorObj (M.obj (op PUnit.unit)) (N.obj PUnit.unit) r s n hn (m ⊗ₜ[A] v)))
    (ι_ringIso_hom A M N)

@[reassoc]
lemma ringIso_naturality {M M' : ModuleCategory A PUnit.{1}}
    {N N' : LeftModuleCategory A PUnit.{1}} (f : M ⟶ M') (g : N ⟶ N') :
    map A PUnit.{1} f g ≫
      (ringIso A (ForgetEnrichment.to (Complex A) M') (ForgetEnrichment.to (Complex A) N')).hom =
    (ringIso A (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N)).hom ≫
      ((moduleEvaluation A PUnit.{1} PUnit.unit).map f ⊗ₘ
        (leftModuleEvaluation A PUnit.{1} PUnit.unit).map g) := by
  apply (cancel_epi (ringIso A (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) N)).inv).mp
  change ι A PUnit.{1} (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N) PUnit.unit ≫ map A PUnit.{1} f g ≫
        (ringIso A (ForgetEnrichment.to (Complex A) M')
          (ForgetEnrichment.to (Complex A) N')).hom =
    ι A PUnit.{1} (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N) PUnit.unit ≫
        (ringIso A (ForgetEnrichment.to (Complex A) M)
          (ForgetEnrichment.to (Complex A) N)).hom ≫ _
  rw [ι_map_assoc, ι_ringIso_hom, ι_ringIso_hom_assoc]
  let fx : (ForgetEnrichment.to (Complex A) M).obj (op PUnit.unit) ⟶
      (ForgetEnrichment.to (Complex A) M').obj (op PUnit.unit) :=
    (moduleEvaluation A PUnit.{1} PUnit.unit).map f
  let gx : (ForgetEnrichment.to (Complex A) N).obj PUnit.unit ⟶
      (ForgetEnrichment.to (Complex A) N').obj PUnit.unit :=
    (leftModuleEvaluation A PUnit.{1} PUnit.unit).map g
  change (fx ⊗ₘ gx) ≫ 𝟙 _ = fx ⊗ₘ gx
  exact Category.comp_id _

/-- 指定した非有界複体二つに対する既存cochainTensorとの比較。 -/
abbrev ringComplexTensorIso (P Q : Complex A) :
    obj A PUnit.{1} (ringModule A P) (ringLeftModule A Q) ≅
      SerrePositivity.cochainTensor P Q := ringIso A (ringModule A P) (ringLeftModule A Q)

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end Ring

/-! ## Yoneda（旧 SerrePositivity/DifferentialGraded/Tensor/Yoneda.lean） -/

/-! # representableとbalanced tensorのYoneda評価 -/

@[expose] public section Yoneda
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Limits MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

omit [Small.{u} D] in
/-- representableの右作用は、二つのHomの順を交換した豊穣合成。 -/
lemma representable_rightAction (z x y : D) :
    rightAction A D (representable A z) x y =
      (signedSwap (y ⟶[Complex A] z) (x ⟶[Complex A] y)).hom ≫
        eComp (Complex A) x y z := by
  unfold rightAction moduleActionChain
  change (signedSwap (y ⟶[Complex A] z) (x ⟶[Complex A] y)).hom ≫
    uncurryRight (curryRight (eComp (Complex A) x y z)) = _
  rw [uncurryRight_curryRight]

/-- 左加群の作用はrepresentable tensorに対するbalanced族を与える。 -/
def yonedaFamily (z : D) (N : LeftModule A D) :
    BalancedFamily A D (representable A z) N (N.obj z) := by
  refine ⟨fun x => leftAction A D N x z, ?_⟩
  intro x y
  apply triple_ext
  intro a p b n hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro h f t
  change (leftAction A D N x z).f n
    ((rightAction A D (representable A z) x y ▷ N.obj x).f n
      (ιTensorObj ((y ⟶[Complex A] z) ⊗ (x ⟶[Complex A] y)) (N.obj x)
        (a + p) b n hn
        (ιTensorObj (y ⟶[Complex A] z) (x ⟶[Complex A] y) a p (a + p) rfl
          (h ⊗ₜ[A] f) ⊗ₜ[A] t))) =
    (leftAction A D N y z).f n
      (((y ⟶[Complex A] z) ◁ leftAction A D N x y).f n
        ((α_ (y ⟶[Complex A] z) (x ⟶[Complex A] y) (N.obj x)).hom.f n
          (ιTensorObj ((y ⟶[Complex A] z) ⊗ (x ⟶[Complex A] y)) (N.obj x)
            (a + p) b n hn
            (ιTensorObj (y ⟶[Complex A] z) (x ⟶[Complex A] y) a p (a + p) rfl
              (h ⊗ₜ[A] f) ⊗ₜ[A] t))))
  rw [whiskerRight_apply, rightAction_apply, associator_apply,
    whiskerLeft_apply, leftAction_apply]
  change SerrePositivity.DifferentialGraded.leftAction A N
    ((a * p).negOnePow • forward A (n := a + p) f h (by omega)) t (by omega) = _
  rw [leftAction_apply, leftAction_apply]
  have hs : SerrePositivity.DifferentialGraded.leftAction A N (n := n)
      ((a * p).negOnePow • forward A (n := a + p) f h (by omega)) t (by omega) =
    (a * p).negOnePow • SerrePositivity.DifferentialGraded.leftAction A N (n := n)
      (forward A f h (show p + a = a + p by omega)) t (by omega) := by
    simp only [SerrePositivity.DifferentialGraded.leftAction, Units.smul_def,
      map_zsmul]
    rfl
  rw [hs, SerrePositivity.DifferentialGraded.leftAction_forward A N f h t
    (show p + a = a + p by omega) (show b + p = p + b by omega) (by omega)]
  simp only [smul_smul, mul_comm p a, Int.units_mul_self, one_smul]

/-- representable tensorを評価複体へ送るYoneda写像。 -/
def yonedaEvaluation (z : D) (N : LeftModule A D) :
    obj A D (representable A z) N ⟶ N.obj z :=
  desc A D (representable A z) N (yonedaFamily A D z N)

@[reassoc (attr := simp)]
lemma ι_yonedaEvaluation (z : D) (N : LeftModule A D) (x : D) :
    ι A D (representable A z) N x ≫ yonedaEvaluation A D z N = leftAction A D N x z :=
  ι_desc A D (representable A z) N (yonedaFamily A D z N) x

lemma yonedaEvaluation_element (z : D) (N : LeftModule A D) (x : D)
    {p q n : ℤ} (f : GradedHom A x z p) (t : (N.obj x).X q) (hn : p + q = n) :
    (yonedaEvaluation A D z N).f n (element A D (representable A z) N x f t hn) =
      SerrePositivity.DifferentialGraded.leftAction A N f t (by omega) := by
  have h := congrArg (fun k => k.f n
    (ιTensorObj (x ⟶[Complex A] z) (N.obj x) p q n hn (f ⊗ₜ[A] t)))
    (ι_yonedaEvaluation A D z N x)
  exact h.trans (leftAction_apply A D N x z p q n hn f t)

/-- 単位Homを挿入するYoneda評価の逆向きの射。 -/
def yonedaInsertion (z : D) (N : LeftModule A D) :
    N.obj z ⟶ obj A D (representable A z) N :=
  freeUnitInsert A z (N.obj z) ≫
    (signedSwap (N.obj z) (z ⟶[Complex A] z)).hom ≫ ι A D (representable A z) N z

lemma yonedaInsertion_apply (z : D) (N : LeftModule A D) (q : ℤ) (t : (N.obj z).X q) :
    (yonedaInsertion A D z N).f q t =
      element A D (representable A z) N z (unitElement A z).val t (zero_add q) := by
  change (ι A D (representable A z) N z).f q
    ((signedSwap (N.obj z) (z ⟶[Complex A] z)).hom.f q
      ((freeUnitInsert A z (N.obj z)).f q t)) = _
  rw [freeUnitInsert_apply, signedSwap_apply]
  simp only [mul_zero, Int.negOnePow_zero, one_smul]
  rfl

@[reassoc (attr := simp)]
lemma yonedaInsertion_evaluation (z : D) (N : LeftModule A D) :
    yonedaInsertion A D z N ≫ yonedaEvaluation A D z N = 𝟙 (N.obj z) := by
  apply HomologicalComplex.hom_ext
  intro q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  change (yonedaEvaluation A D z N).f q ((yonedaInsertion A D z N).f q t) = t
  rw [yonedaInsertion_apply, yonedaEvaluation_element]
  exact SerrePositivity.DifferentialGraded.leftAction_unit A N z q t

@[reassoc (attr := simp)]
lemma yonedaEvaluation_insertion (z : D) (N : LeftModule A D) :
    yonedaEvaluation A D z N ≫ yonedaInsertion A D z N = 𝟙 _ := by
  apply hom_ext
  intro x
  apply tensorHom_ext
  intro p q n hn
  subst n
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f t
  change (yonedaInsertion A D z N).f (p + q)
    ((yonedaEvaluation A D z N).f (p + q) (element A D (representable A z) N x f t rfl)) =
      element A D (representable A z) N x f t rfl
  rw [yonedaEvaluation_element, yonedaInsertion_apply]
  have h := congrArg (fun k => k.f (p + q)
    (ιTensorObj ((z ⟶[Complex A] z) ⊗ (x ⟶[Complex A] z)) (N.obj x) p q (p + q) rfl
      (ιTensorObj (z ⟶[Complex A] z) (x ⟶[Complex A] z) 0 p p (zero_add p)
        ((unitElement A z).val ⊗ₜ[A] f) ⊗ₜ[A] t)))
    (condition A D (representable A z) N x z)
  change (ι A D (representable A z) N x).f (p + q)
    ((rightAction A D (representable A z) x z ▷ N.obj x).f (p + q)
      (ιTensorObj ((z ⟶[Complex A] z) ⊗ (x ⟶[Complex A] z)) (N.obj x) p q (p + q) rfl
        (ιTensorObj (z ⟶[Complex A] z) (x ⟶[Complex A] z) 0 p p (zero_add p)
          ((unitElement A z).val ⊗ₜ[A] f) ⊗ₜ[A] t))) =
    (ι A D (representable A z) N z).f (p + q)
      (((z ⟶[Complex A] z) ◁ leftAction A D N x z).f (p + q)
        ((α_ (z ⟶[Complex A] z) (x ⟶[Complex A] z) (N.obj x)).hom.f (p + q)
          (ιTensorObj ((z ⟶[Complex A] z) ⊗ (x ⟶[Complex A] z)) (N.obj x) p q (p + q) rfl
            (ιTensorObj (z ⟶[Complex A] z) (x ⟶[Complex A] z) 0 p p (zero_add p)
              ((unitElement A z).val ⊗ₜ[A] f) ⊗ₜ[A] t)))) at h
  rw [whiskerRight_apply, rightAction_apply, associator_apply_of_sum,
    whiskerLeft_apply, leftAction_apply] at h
  simp only [zero_mul, Int.negOnePow_zero, one_smul] at h
  change element A D (representable A z) N x
    (forward A f (unitElement A z).val (add_zero p)) t rfl = _ at h
  simpa only [element, unit_forward] using h.symm


/-- 右representableとのbalanced tensorは評価複体に同型。 -/
def yonedaIso (z : D) (N : LeftModule A D) :
    obj A D (representable A z) N ≅ N.obj z where
  hom := yonedaEvaluation A D z N
  inv := yonedaInsertion A D z N
  hom_inv_id := yonedaEvaluation_insertion A D z N
  inv_hom_id := yonedaInsertion_evaluation A D z N

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end Yoneda

/-! ## Parameter（旧 SerrePositivity/DifferentialGraded/Tensor/Parameter.lean） -/

/-! # パラメータ付きbalanced族の降下と普遍性 -/

@[expose] public section Parameter
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end Parameter

/-! ## ParameterLeftAction（旧 SerrePositivity/DifferentialGraded/Tensor/ParameterLeftAction.lean） -/

/-! # 全次数自然変換と左tensor作用の交換 -/

@[expose] public section ParameterLeftAction
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

lemma paramLeftAction {K : Complex A} {N N' : LeftModule A D}
    (a : ∀ x : D, K ⟶ homComplex A (N.obj x) (N'.obj x))
    (ha : ∀ x y : D, (β_ K (x ⟶[Complex A] y)).hom ≫
      (N.map x y ⊗ₘ a y) ≫ enrichedComposition _ _ _ =
        (a x ⊗ₘ N'.map x y) ≫ enrichedComposition _ _ _) (x y : D) :
    (α_ K (x ⟶[Complex A] y) (N.obj x)).hom ≫
      (K ◁ leftAction A D N x y) ≫ uncurryRight (a y) =
    ((signedSwap K (x ⟶[Complex A] y)).hom ▷ N.obj x) ≫
      (α_ (x ⟶[Complex A] y) K (N.obj x)).hom ≫
        ((x ⟶[Complex A] y) ◁ uncurryRight (a x)) ≫ leftAction A D N' x y := by
  apply triple_ext
  intro k p r n hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro t f m
  change (uncurryRight (a y)).f n
    ((K ◁ leftAction A D N x y).f n
      ((α_ K (x ⟶[Complex A] y) (N.obj x)).hom.f n
        (ιTensorObj (K ⊗ (x ⟶[Complex A] y)) (N.obj x) (k + p) r n hn
          (ιTensorObj K (x ⟶[Complex A] y) k p (k + p) rfl (t ⊗ₜ[A] f) ⊗ₜ[A] m)))) =
    (leftAction A D N' x y).f n
      (((x ⟶[Complex A] y) ◁ uncurryRight (a x)).f n
        ((α_ (x ⟶[Complex A] y) K (N.obj x)).hom.f n
          (((signedSwap K (x ⟶[Complex A] y)).hom ▷ N.obj x).f n
            (ιTensorObj (K ⊗ (x ⟶[Complex A] y)) (N.obj x) (k + p) r n hn
              (ιTensorObj K (x ⟶[Complex A] y) k p (k + p) rfl
                (t ⊗ₜ[A] f) ⊗ₜ[A] m)))))
  rw [associator_apply, whiskerLeft_apply, leftAction_apply, uncurryRight_apply,
    whiskerRight_apply, signedSwap_apply]
  simp only [Units.smul_def, ← TensorProduct.smul_tmul', map_zsmul]
  rw [associator_apply_of_sum, whiskerLeft_apply, uncurryRight_apply, leftAction_apply]
  change ((a y).f k t).v (p + r) n (by omega)
      (SerrePositivity.DifferentialGraded.leftAction A N f m (by omega)) =
    (k * p).negOnePow • SerrePositivity.DifferentialGraded.leftAction A N' f
      (((a x).f k t).v r (k + r) (by omega) m) (by omega)
  exact leftParamNaturality_apply_of_sum A a ha t f m (by omega) (by omega) (by omega)

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end ParameterLeftAction

/-! ## ParameterLeft（旧 SerrePositivity/DifferentialGraded/Tensor/ParameterLeft.lean） -/

/-! # 左加群変数のパラメータ付きbalanced tensor作用 -/

@[expose] public section ParameterLeft
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 左加群の全次数自然なHom族を右加群値の後へ移してbalanced族にする。 -/
def leftParamFamily {K : Complex A} {N N' : LeftModule A D} (M : RightModule A D)
    (a : ∀ x : D, K ⟶ homComplex A (N.obj x) (N'.obj x))
    (ha : ∀ x y : D, (β_ K (x ⟶[Complex A] y)).hom ≫
      (N.map x y ⊗ₘ a y) ≫ enrichedComposition _ _ _ =
        (a x ⊗ₘ N'.map x y) ≫ enrichedComposition _ _ _) :
    ParamFamily A D M N K (obj A D M N') := by
  refine ⟨fun x => parameterCross K (M.obj (op x)) (N.obj x) ≫
    (M.obj (op x) ◁ uncurryRight (a x)) ≫ ι A D M N' x, ?_⟩
  intro x y
  have h := congrArg (fun t => (α_ K (x ⟶[Complex A] y) (N.obj x)).inv ≫ t)
    (paramLeftAction A D a ha x y)
  simp only [Iso.inv_hom_id_assoc] at h
  have hc : (K ◁ leftAction A D N x y) ≫ uncurryRight (a y) =
      parameterCross K (x ⟶[Complex A] y) (N.obj x) ≫
        ((x ⟶[Complex A] y) ◁ uncurryRight (a x)) ≫ leftAction A D N' x y := by
    simpa only [parameterCross, Category.assoc] using h
  dsimp only
  rw [parameterCross_naturality_left_assoc, ← whisker_exchange_assoc,
    condition, associator_naturality_right_assoc, parameterCross_tensor_assoc,
    ← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc]
  simp only [Category.assoc]
  rw [← hc, whiskerLeft_comp, Category.assoc, ← parameterCross_naturality_right_assoc,
    ← whiskerLeft_comp_assoc]

/-- K⊗(M⊗_D N)からM⊗_D N'への実際のchain map。 -/
def leftParamMap {K : Complex A} {N N' : LeftModule A D} (M : RightModule A D)
    (a : ∀ x : D, K ⟶ homComplex A (N.obj x) (N'.obj x))
    (ha : ∀ x y : D, (β_ K (x ⟶[Complex A] y)).hom ≫
      (N.map x y ⊗ₘ a y) ≫ enrichedComposition _ _ _ =
        (a x ⊗ₘ N'.map x y) ≫ enrichedComposition _ _ _) :
    K ⊗ obj A D M N ⟶ obj A D M N' :=
  paramDesc A D M N (leftParamFamily A D M a ha)

@[reassoc (attr := simp)]
lemma ι_leftParamMap {K : Complex A} {N N' : LeftModule A D} (M : RightModule A D)
    (a : ∀ x : D, K ⟶ homComplex A (N.obj x) (N'.obj x))
    (ha : ∀ x y : D, (β_ K (x ⟶[Complex A] y)).hom ≫
      (N.map x y ⊗ₘ a y) ≫ enrichedComposition _ _ _ =
        (a x ⊗ₘ N'.map x y) ≫ enrichedComposition _ _ _) (x : D) :
    (K ◁ ι A D M N x) ≫ leftParamMap A D M a ha =
      parameterCross K (M.obj (op x)) (N.obj x) ≫
        (M.obj (op x) ◁ uncurryRight (a x)) ≫ ι A D M N' x :=
  ι_paramDesc A D M N (leftParamFamily A D M a ha) x

/-- Kと右加群値の次数の積が左変数作用の符号になる。 -/
lemma leftParamMap_element {K : Complex A} {N N' : LeftModule A D} (M : RightModule A D)
    (a : ∀ x : D, K ⟶ homComplex A (N.obj x) (N'.obj x))
    (ha : ∀ x y : D, (β_ K (x ⟶[Complex A] y)).hom ≫
      (N.map x y ⊗ₘ a y) ≫ enrichedComposition _ _ _ =
        (a x ⊗ₘ N'.map x y) ≫ enrichedComposition _ _ _) (x : D)
    {k r s n : ℤ} (t : K.X k) (m : (M.obj (op x)).X r) (v : (N.obj x).X s)
    (hn : k + (r + s) = n) :
    (leftParamMap A D M a ha).f n
      (ιTensorObj K (obj A D M N) k (r + s) n hn
        (t ⊗ₜ[A] element A D M N x m v rfl)) =
    (k * r).negOnePow • element A D M N' x m
      (((a x).f k t).v s (k + s) (by omega) v) (by omega) := by
  have h := congrArg (fun f => f.f n
    (ιTensorObj K (M.obj (op x) ⊗ N.obj x) k (r + s) n hn
      (t ⊗ₜ[A] ιTensorObj (M.obj (op x)) (N.obj x) r s (r + s) rfl (m ⊗ₜ[A] v))))
    (ι_leftParamMap A D M a ha x)
  change (leftParamMap A D M a ha).f n
    ((K ◁ ι A D M N x).f n
      (ιTensorObj K (M.obj (op x) ⊗ N.obj x) k (r + s) n hn
        (t ⊗ₜ[A] ιTensorObj (M.obj (op x)) (N.obj x) r s (r + s) rfl (m ⊗ₜ[A] v)))) =
    (ι A D M N' x).f n
      ((M.obj (op x) ◁ uncurryRight (a x)).f n
        ((parameterCross K (M.obj (op x)) (N.obj x)).f n
          (ιTensorObj K (M.obj (op x) ⊗ N.obj x) k (r + s) n hn
            (t ⊗ₜ[A] ιTensorObj (M.obj (op x)) (N.obj x) r s (r + s) rfl
              (m ⊗ₜ[A] v))))) at h
  rw [whiskerLeft_apply, parameterCross_apply] at h
  simp only [Units.smul_def, map_zsmul] at h
  rw [whiskerLeft_apply, uncurryRight_apply] at h
  simpa only [element, Units.smul_def] using h

/-- 左加群の主Hom複体からbalanced tensorの主Hom複体への射。 -/
def leftHomMap (M : RightModule A D) (N N' : LeftModule A D) :
    leftModuleHom A D N N' ⟶ homComplex A (obj A D M N) (obj A D M N') :=
  paramHomMap A D M N (leftParamFamily A D M
    (leftModuleHomπ A D N N') (leftModuleHomπ_naturality A D N N'))

@[reassoc]
lemma leftHomMap_ι (M : RightModule A D) (N N' : LeftModule A D) (x : D) :
    leftHomMap A D M N N' ≫ homPrecompose (ι A D M N x) (obj A D M N') =
    curryRight (parameterCross (leftModuleHom A D N N') (M.obj (op x)) (N.obj x) ≫
      (M.obj (op x) ◁ uncurryRight (leftModuleHomπ A D N N' x)) ≫ ι A D M N' x) :=
  paramHomMap_ι A D M N (leftParamFamily A D M
    (leftModuleHomπ A D N N') (leftModuleHomπ_naturality A D N N')) x

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end ParameterLeft

/-! ## ParameterRightAction（旧 SerrePositivity/DifferentialGraded/Tensor/ParameterRightAction.lean） -/

/-! # 全次数自然変換とbalanced tensorの右作用 -/

@[expose] public section ParameterRightAction
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

omit [Small.{u} D] in
/-- Kパラメータの全次数自然変換は右tensor作用と結合的に可換。 -/
lemma paramRightAction {K : Complex A} {M M' : RightModule A D}
    (a : ∀ x : Dᵒᵖ, K ⟶ homComplex A (M.obj x) (M'.obj x))
    (ha : ∀ x y : Dᵒᵖ, (β_ K (x ⟶[Complex A] y)).hom ≫
      (M.map x y ⊗ₘ a y) ≫ enrichedComposition _ _ _ =
        (a x ⊗ₘ M'.map x y) ≫ enrichedComposition _ _ _) (x y : D) :
    (α_ K (M.obj (op y)) (x ⟶[Complex A] y)).hom ≫
      (K ◁ rightAction A D M x y) ≫ uncurryRight (a (op x)) =
    (uncurryRight (a (op y)) ▷ (x ⟶[Complex A] y)) ≫ rightAction A D M' x y := by
  apply triple_ext
  intro k r p n hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro t m f
  change (uncurryRight (a (op x))).f n
    ((K ◁ rightAction A D M x y).f n
      ((α_ K (M.obj (op y)) (x ⟶[Complex A] y)).hom.f n
        (ιTensorObj (K ⊗ M.obj (op y)) (x ⟶[Complex A] y) (k + r) p n hn
          (ιTensorObj K (M.obj (op y)) k r (k + r) rfl (t ⊗ₜ[A] m) ⊗ₜ[A] f)))) =
    (rightAction A D M' x y).f n
      ((uncurryRight (a (op y)) ▷ (x ⟶[Complex A] y)).f n
        (ιTensorObj (K ⊗ M.obj (op y)) (x ⟶[Complex A] y) (k + r) p n hn
          (ιTensorObj K (M.obj (op y)) k r (k + r) rfl (t ⊗ₜ[A] m) ⊗ₜ[A] f)))
  rw [associator_apply, whiskerLeft_apply, rightAction_apply,
    whiskerRight_apply, uncurryRight_apply, rightAction_apply]
  rw [uncurryRight_apply]
  simp only [Units.smul_def, map_zsmul]
  change (r * p).negOnePow •
      (((a (op x)).f k t).v (r + p) n (by omega) (moduleAction A M f m rfl)) =
    ((k + r) * p).negOnePow • moduleAction A M' f
      (((a (op y)).f k t).v r (k + r) (by omega) m) hn
  have h := moduleParamNaturality_apply_of_sum A a ha t f m
    (show k + p = k + p from rfl) (show r + (k + p) = n by omega)
    (show r + p = r + p from rfl) (show r + k = k + r by omega)
  rw [h]
  simp only [smul_smul, ← Int.negOnePow_add]
  congr 1
  congr 1
  ring

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end ParameterRightAction

/-! ## ParameterRight（旧 SerrePositivity/DifferentialGraded/Tensor/ParameterRight.lean） -/

/-! # 右加群変数のパラメータ付きbalanced tensor作用 -/

@[expose] public section ParameterRight
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全次数自然な右加群射の族はbalanced族を誘導する。 -/
def rightParamFamily {K : Complex A} {M M' : RightModule A D} (N : LeftModule A D)
    (a : ∀ x : Dᵒᵖ, K ⟶ homComplex A (M.obj x) (M'.obj x))
    (ha : ∀ x y : Dᵒᵖ, (β_ K (x ⟶[Complex A] y)).hom ≫
      (M.map x y ⊗ₘ a y) ≫ enrichedComposition _ _ _ =
        (a x ⊗ₘ M'.map x y) ≫ enrichedComposition _ _ _) :
    ParamFamily A D M N K (obj A D M' N) := by
  refine ⟨fun x => (α_ K (M.obj (op x)) (N.obj x)).inv ≫
    (uncurryRight (a (op x)) ▷ N.obj x) ≫ ι A D M' N x, ?_⟩
  intro x y
  have h := congrArg (fun t => (α_ K (M.obj (op y)) (x ⟶[Complex A] y)).inv ≫ t)
    (paramRightAction A D a ha x y)
  simp only [Iso.inv_hom_id_assoc] at h
  dsimp only
  rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc, h,
    comp_whiskerRight, comp_whiskerRight]
  simp only [Category.assoc]
  rw [condition, associator_naturality_left_assoc,
    pentagon_inv_inv_hom_hom_inv_assoc,
    ← whisker_exchange_assoc, ← associator_inv_naturality_right_assoc,
    ← whiskerLeft_comp_assoc]

/-- K⊗(M⊗_D N)からM'⊗_D Nへの実際のchain map。 -/
def rightParamMap {K : Complex A} {M M' : RightModule A D} (N : LeftModule A D)
    (a : ∀ x : Dᵒᵖ, K ⟶ homComplex A (M.obj x) (M'.obj x))
    (ha : ∀ x y : Dᵒᵖ, (β_ K (x ⟶[Complex A] y)).hom ≫
      (M.map x y ⊗ₘ a y) ≫ enrichedComposition _ _ _ =
        (a x ⊗ₘ M'.map x y) ≫ enrichedComposition _ _ _) :
    K ⊗ obj A D M N ⟶ obj A D M' N :=
  paramDesc A D M N (rightParamFamily A D N a ha)

@[reassoc (attr := simp)]
lemma ι_rightParamMap {K : Complex A} {M M' : RightModule A D} (N : LeftModule A D)
    (a : ∀ x : Dᵒᵖ, K ⟶ homComplex A (M.obj x) (M'.obj x))
    (ha : ∀ x y : Dᵒᵖ, (β_ K (x ⟶[Complex A] y)).hom ≫
      (M.map x y ⊗ₘ a y) ≫ enrichedComposition _ _ _ =
        (a x ⊗ₘ M'.map x y) ≫ enrichedComposition _ _ _) (x : D) :
    (K ◁ ι A D M N x) ≫ rightParamMap A D N a ha =
      (α_ K (M.obj (op x)) (N.obj x)).inv ≫
        (uncurryRight (a (op x)) ▷ N.obj x) ≫ ι A D M' N x :=
  ι_paramDesc A D M N (rightParamFamily A D N a ha) x

lemma rightParamMap_element {K : Complex A} {M M' : RightModule A D} (N : LeftModule A D)
    (a : ∀ x : Dᵒᵖ, K ⟶ homComplex A (M.obj x) (M'.obj x))
    (ha : ∀ x y : Dᵒᵖ, (β_ K (x ⟶[Complex A] y)).hom ≫
      (M.map x y ⊗ₘ a y) ≫ enrichedComposition _ _ _ =
        (a x ⊗ₘ M'.map x y) ≫ enrichedComposition _ _ _) (x : D)
    {k r s n : ℤ} (t : K.X k) (m : (M.obj (op x)).X r) (v : (N.obj x).X s)
    (hn : k + (r + s) = n) :
    (rightParamMap A D N a ha).f n
      (ιTensorObj K (obj A D M N) k (r + s) n hn
        (t ⊗ₜ[A] element A D M N x m v rfl)) =
    element A D M' N x (((a (op x)).f k t).v r (k + r) (by omega) m) v (by omega) := by
  have h := congrArg (fun f => f.f n
    (ιTensorObj K (M.obj (op x) ⊗ N.obj x) k (r + s) n hn
      (t ⊗ₜ[A] ιTensorObj (M.obj (op x)) (N.obj x) r s (r + s) rfl (m ⊗ₜ[A] v))))
    (ι_rightParamMap A D N a ha x)
  change (rightParamMap A D N a ha).f n
    ((K ◁ ι A D M N x).f n
      (ιTensorObj K (M.obj (op x) ⊗ N.obj x) k (r + s) n hn
        (t ⊗ₜ[A] ιTensorObj (M.obj (op x)) (N.obj x) r s (r + s) rfl (m ⊗ₜ[A] v)))) =
    (ι A D M' N x).f n
      ((uncurryRight (a (op x)) ▷ N.obj x).f n
        ((α_ K (M.obj (op x)) (N.obj x)).inv.f n
          (ιTensorObj K (M.obj (op x) ⊗ N.obj x) k (r + s) n hn
            (t ⊗ₜ[A] ιTensorObj (M.obj (op x)) (N.obj x) r s (r + s) rfl
              (m ⊗ₜ[A] v))))) at h
  rw [whiskerLeft_apply, associator_inv_apply, whiskerRight_apply, uncurryRight_apply] at h
  exact h

/-- 右加群の主Hom複体からbalanced tensorの主Hom複体への射。 -/
def rightHomMap (M M' : RightModule A D) (N : LeftModule A D) :
    moduleHom A D M M' ⟶ homComplex A (obj A D M N) (obj A D M' N) :=
  paramHomMap A D M N (rightParamFamily A D N
    (fun x => moduleHomπ A D M M' x.unop) (moduleHomπ_naturality A D M M'))

@[reassoc]
lemma rightHomMap_ι (M M' : RightModule A D) (N : LeftModule A D) (x : D) :
    rightHomMap A D M M' N ≫ homPrecompose (ι A D M N x) (obj A D M' N) =
    curryRight ((α_ (moduleHom A D M M') (M.obj (op x)) (N.obj x)).inv ≫
      (uncurryRight (moduleHomπ A D M M' x) ▷ N.obj x) ≫ ι A D M' N x) :=
  paramHomMap_ι A D M N (rightParamFamily A D N
    (fun x => moduleHomπ A D M M' x.unop) (moduleHomπ_naturality A D M M')) x

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end ParameterRight

/-! ## ParameterBalancedElements（旧 SerrePositivity/DifferentialGraded/Tensor/ParameterBalancedElements.lean） -/

/-! # パラメータ付きbalanced関係の斉次生成元公式 -/

@[expose] public section ParameterBalancedElements
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 左パラメータを固定したbalanced関係。パラメータの次数による余分な符号はない。 -/
lemma paramFamily_balanced_element {M : RightModule A D} {N : LeftModule A D}
    {K T : Complex A} (a : ParamFamily A D M N K T) (x y : D)
    {k r p s n : ℤ} (t : K.X k) (m : (M.obj (op y)).X r)
    (f : GradedHom A x y p) (v : (N.obj x).X s) (hn : k + (r + p + s) = n) :
    (r * p).negOnePow • (a.val x).f n
      (ιTensorObj K (M.obj (op x) ⊗ N.obj x) k (r + p + s) n hn
        (t ⊗ₜ[A] ιTensorObj (M.obj (op x)) (N.obj x) (r + p) s (r + p + s) rfl
          (moduleAction A M f m rfl ⊗ₜ[A] v))) =
    (a.val y).f n
      (ιTensorObj K (M.obj (op y) ⊗ N.obj y) k (r + p + s) n (by omega)
        (t ⊗ₜ[A] ιTensorObj (M.obj (op y)) (N.obj y) r (p + s) (r + p + s) (by omega)
          (m ⊗ₜ[A] SerrePositivity.DifferentialGraded.leftAction A N
            (n := p + s) f v (by omega)))) := by
  rcases a with ⟨a, ha⟩
  have h := congrArg (fun z => z.f n
    (ιTensorObj K ((M.obj (op y) ⊗ (x ⟶[Complex A] y)) ⊗ N.obj x)
      k (r + p + s) n hn
      (t ⊗ₜ[A] ιTensorObj (M.obj (op y) ⊗ (x ⟶[Complex A] y)) (N.obj x)
        (r + p) s (r + p + s) rfl
        (ιTensorObj (M.obj (op y)) (x ⟶[Complex A] y) r p (r + p) rfl
          (m ⊗ₜ[A] f) ⊗ₜ[A] v)))) (ha x y)
  simp only [comp_f, ModuleCat.comp_apply, whiskerLeft_comp] at h
  rw [whiskerLeft_apply, whiskerRight_apply, rightAction_apply,
    whiskerLeft_apply, associator_apply, whiskerLeft_apply, whiskerLeft_apply,
    leftAction_apply] at h
  have ht (z : (M.obj (op x) ⊗ N.obj x).X (r + p + s)) (i : ℤ) :
      t ⊗ₜ[A] (i • z) = i • (t ⊗ₜ[A] z) :=
    map_zsmul (TensorProduct.mk A _ _ t) i z
  simpa only [Units.smul_def, ← TensorProduct.smul_tmul', map_zsmul, ht] using h

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end ParameterBalancedElements

/-! ## ParameterBalancedConstructor（旧 SerrePositivity/DifferentialGraded/Tensor/ParameterBalancedConstructor.lean） -/

/-! # パラメータ付きbalanced族の斉次生成元からの構成 -/

@[expose] public section ParameterBalancedConstructor
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A]

/-- 固定次数の三重tensorからの線形射を純粋生成元で判定する。 -/
lemma triple_degree_linear_ext (P Q S : Complex A) (i : ℤ) {V : ModuleCat.{u} A}
    (f g : ((P ⊗ Q) ⊗ S).X i →ₗ[A] V)
    (h : ∀ (r p s : ℤ) (hi : r + p + s = i)
      (m : P.X r) (q : Q.X p) (v : S.X s),
      f (ιTensorObj (P ⊗ Q) S (r + p) s i hi
        (ιTensorObj P Q r p (r + p) rfl (m ⊗ₜ[A] q) ⊗ₜ[A] v)) =
      g (ιTensorObj (P ⊗ Q) S (r + p) s i hi
        (ιTensorObj P Q r p (r + p) rfl (m ⊗ₜ[A] q) ⊗ₜ[A] v))) : f = g := by
  have heq : ModuleCat.ofHom f = ModuleCat.ofHom g := by
    apply SerrePositivity.cochainTensorTriple_hom_ext P Q S i
    intro r p s hi
    apply ModuleCat.hom_ext
    apply TensorProduct.ext_threefold
    intro m q v
    exact h r p s hi m q v
  exact congrArg ModuleCat.Hom.hom heq

variable (D : Type v) [DGCategory A D]

/-- パラメータ付きの純粋生成元関係から、chain map族のbalanced性を復元する。 -/
def paramFamilyMk {M : RightModule A D} {N : LeftModule A D} {K T : Complex A}
    (a : ∀ x, K ⊗ (M.obj (op x) ⊗ N.obj x) ⟶ T)
    (hbal : ∀ (x y : D) (k r p s n : ℤ) (hn : k + (r + p + s) = n)
      (t : K.X k) (m : (M.obj (op y)).X r) (f : GradedHom A x y p) (v : (N.obj x).X s),
      (r * p).negOnePow • (a x).f n
        (ιTensorObj K (M.obj (op x) ⊗ N.obj x) k (r + p + s) n hn
          (t ⊗ₜ[A] ιTensorObj (M.obj (op x)) (N.obj x) (r + p) s (r + p + s) rfl
            (moduleAction A M f m rfl ⊗ₜ[A] v))) =
      (a y).f n
        (ιTensorObj K (M.obj (op y) ⊗ N.obj y) k (r + p + s) n (by omega)
          (t ⊗ₜ[A] ιTensorObj (M.obj (op y)) (N.obj y) r (p + s) (r + p + s) (by omega)
            (m ⊗ₜ[A] SerrePositivity.DifferentialGraded.leftAction A N
              (n := p + s) f v (by omega))))) : ParamFamily A D M N K T := by
  refine ⟨a, ?_⟩
  intro x y
  apply HomologicalComplex.Hom.ext
  funext n
  apply mapBifunctor.hom_ext
  intro k i hki
  apply ModuleCat.hom_ext
  apply TensorProduct.curry_injective
  apply LinearMap.ext
  intro t
  apply triple_degree_linear_ext A (M.obj (op y)) (x ⟶[Complex A] y) (N.obj x) i
  intro r p s hi m f v
  subst i
  change (a x).f n
    ((K ◁ (rightAction A D M x y ▷ N.obj x)).f n
      (ιTensorObj K ((M.obj (op y) ⊗ (x ⟶[Complex A] y)) ⊗ N.obj x)
        k (r + p + s) n hki
        (t ⊗ₜ[A] ιTensorObj (M.obj (op y) ⊗ (x ⟶[Complex A] y)) (N.obj x)
          (r + p) s (r + p + s) rfl
          (ιTensorObj (M.obj (op y)) (x ⟶[Complex A] y) r p (r + p) rfl
            (m ⊗ₜ[A] f) ⊗ₜ[A] v)))) =
    (a y).f n
      ((K ◁ ((α_ (M.obj (op y)) (x ⟶[Complex A] y) (N.obj x)).hom ≫
        M.obj (op y) ◁ leftAction A D N x y)).f n
        (ιTensorObj K ((M.obj (op y) ⊗ (x ⟶[Complex A] y)) ⊗ N.obj x)
          k (r + p + s) n hki
          (t ⊗ₜ[A] ιTensorObj (M.obj (op y) ⊗ (x ⟶[Complex A] y)) (N.obj x)
            (r + p) s (r + p + s) rfl
            (ιTensorObj (M.obj (op y)) (x ⟶[Complex A] y) r p (r + p) rfl
              (m ⊗ₜ[A] f) ⊗ₜ[A] v))))
  simp only [whiskerLeft_comp, comp_f, ModuleCat.comp_apply]
  rw [whiskerLeft_apply, whiskerRight_apply, rightAction_apply,
    whiskerLeft_apply, associator_apply, whiskerLeft_apply, whiskerLeft_apply, leftAction_apply]
  have ht (z : (M.obj (op x) ⊗ N.obj x).X (r + p + s)) (j : ℤ) :
      t ⊗ₜ[A] (j • z) = j • (t ⊗ₜ[A] z) :=
    map_zsmul (TensorProduct.mk A _ _ t) j z
  simpa only [Units.smul_def, ← TensorProduct.smul_tmul', map_zsmul, ht] using
    hbal x y k r p s n hki t m f v

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end ParameterBalancedConstructor
