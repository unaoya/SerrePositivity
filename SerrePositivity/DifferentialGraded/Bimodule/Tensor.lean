module

public import SerrePositivity.DifferentialGraded.Bimodule.Basic
public import SerrePositivity.DifferentialGraded.Category.TensorMixed
public import SerrePositivity.DifferentialGraded.Functor.ComplexValued
public import SerrePositivity.DifferentialGraded.Complexes.CochainInterchange
public import SerrePositivity.DifferentialGraded.Bimodule.Value
public import SerrePositivity.DifferentialGraded.Module.LeftMapNaturality
public import SerrePositivity.DifferentialGraded.Category.TensorSmall

/-!
# Bimodule.Tensor

## 概要
10 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

universe u v w

/-! ## TensorFunctor（旧 SerrePositivity/DifferentialGraded/Bimodule/TensorFunctor.lean） -/

/-! # tensor積dg圏上の関手の左右への制限 -/

@[expose] public section TensorFunctor

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite CochainComplex HomComplex HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C]

/-- 右B・左C作用をuncurriedに表示する豊穣関手。 -/
abbrev BimoduleTensorFunctor := DGFunctor A (DGTensorCategory A Bᵒᵖ C) (Complex A)

namespace BimoduleTensorFunctor
variable {A B C}

/-- Cの対象を固定して右B加群へ制限する。 -/
def rightAt (F : BimoduleTensorFunctor A B C) (c : C) : RightModule A B :=
  (dgTensorIncludeFirst A Bᵒᵖ C c).comp F

/-- Bの対象を固定して左C加群へ制限する。 -/
def leftAt (F : BimoduleTensorFunctor A B C) (b : B) : LeftModule A C :=
  (dgTensorIncludeSecond A Bᵒᵖ C (op b)).comp F

/-- 制限された二作用は全次数でKoszul交換則を満たす。 -/
lemma interchange (F : BimoduleTensorFunctor A B C) {x y : Bᵒᵖ} {c d : C} {p q : ℤ}
    (f : GradedHom A x y p) (g : GradedHom A c d q) :
    (((F.rightAt c).map x y).f p f).comp (((F.leftAt y.unop).map c d).f q g)
        (by omega : p + q = q + p) =
      (q * p).negOnePow • ((((F.leftAt x.unop).map c d).f q g).comp
        (((F.rightAt d).map x y).f p f) rfl) := by
  change (((F.map (x, c) (y, c)).f p
      ((dgTensorFirstHom A Bᵒᵖ C c x y).f p f)).comp
      ((F.map (y, c) (y, d)).f q ((dgTensorSecondHom A Bᵒᵖ C y c d).f q g))
        (by omega : p + q = q + p)) =
    (q * p).negOnePow • (((F.map (x, c) (x, d)).f q
      ((dgTensorSecondHom A Bᵒᵖ C x c d).f q g)).comp
      ((F.map (x, d) (y, d)).f p ((dgTensorFirstHom A Bᵒᵖ C d x y).f p f)) rfl)
  have h₁ := DGFunctor.map_forward A F (x := (x, c)) (y := (y, c)) (z := (y, d))
    ((dgTensorFirstHom A Bᵒᵖ C c x y).f p f)
    ((dgTensorSecondHom A Bᵒᵖ C y c d).f q g) (by omega : p + q = q + p)
  rw [dgTensor_first_then_second] at h₁
  change (F.map (x, c) (y, d)).f (q + p)
      (dgTensorElement A (x := (x, c)) (y := (y, d)) f g (by omega)) =
    (enrichedComposition (F.obj (x, c)) (F.obj (y, c)) (F.obj (y, d))).f (q + p)
      (ιTensorObj (homComplex A (F.obj (x, c)) (F.obj (y, c)))
        (homComplex A (F.obj (y, c)) (F.obj (y, d))) p q (q + p) (by omega)
        (((F.map (x, c) (y, c)).f p ((dgTensorFirstHom A Bᵒᵖ C c x y).f p f)) ⊗ₜ[A]
          ((F.map (y, c) (y, d)).f q ((dgTensorSecondHom A Bᵒᵖ C y c d).f q g)))) at h₁
  rw [enrichedComposition_apply, mul_comm p q] at h₁
  have h₂ := DGFunctor.map_forward A F (x := (x, c)) (y := (x, d)) (z := (y, d))
    ((dgTensorSecondHom A Bᵒᵖ C x c d).f q g)
    ((dgTensorFirstHom A Bᵒᵖ C d x y).f p f) rfl
  rw [dgTensor_second_then_first] at h₂
  change (F.map (x, c) (y, d)).f (q + p)
      ((q * p).negOnePow • dgTensorElement A (x := (x, c)) (y := (y, d)) f g (by omega)) =
    (enrichedComposition (F.obj (x, c)) (F.obj (x, d)) (F.obj (y, d))).f (q + p)
      (ιTensorObj (homComplex A (F.obj (x, c)) (F.obj (x, d)))
        (homComplex A (F.obj (x, d)) (F.obj (y, d))) q p (q + p) rfl
        (((F.map (x, c) (x, d)).f q ((dgTensorSecondHom A Bᵒᵖ C x c d).f q g)) ⊗ₜ[A]
          ((F.map (x, d) (y, d)).f p ((dgTensorFirstHom A Bᵒᵖ C d x y).f p f)))) at h₂
  rw [enrichedComposition_apply] at h₂
  simp only [Units.smul_def, map_zsmul] at h₁ h₂
  rw [h₁] at h₂
  simpa only [← Units.smul_def, smul_smul, Int.units_mul_self, one_smul] using h₂

variable [Small.{u} B]

/-- 左作用は閉零自然性でなく、右B加群間の全次数自然変換を与える。 -/
def paramTrans (F : BimoduleTensorFunctor A B C) (c d : C) :
    ModuleParamTrans A B (c ⟶[Complex A] d) (F.rightAt c) (F.rightAt d) where
  app b := (F.leftAt b.unop).map c d
  naturality x y := moduleParamNaturality_of_cochain A (D := B)
    (K := c ⟶[Complex A] d) (M := F.rightAt c) (N := F.rightAt d)
    (fun b : Bᵒᵖ => (F.leftAt b.unop).map c d)
    (fun x y k p m hm t f => by
      subst m
      exact F.interchange f t) x y

/-- tensor積上の豊穣関手をcurriedなbimoduleへ変換する。 -/
def toBimodule (F : BimoduleTensorFunctor A B C) : Bimodule A B C :=
  Bimodule.ofParamTrans A B C F.rightAt F.paramTrans
    (fun c b => (F.leftAt b.unop).map_id c)
    (fun c d e b => (F.leftAt b.unop).map_comp c d e)

/-- 得られる左作用の全Hom end評価は元の制限関手のHom射。 -/
lemma toBimodule_map_π (F : BimoduleTensorFunctor A B C) (c d : C) (b : B) :
    F.toBimodule.toFunctor.map c d ≫
      moduleHomπ A B (F.rightAt c) (F.rightAt d) b = (F.leftAt b).map c d :=
  Bimodule.ofParamTrans_map_π A B C F.rightAt F.paramTrans _ _ c d b

end BimoduleTensorFunctor
end SerrePositivity.DifferentialGraded
end

end TensorFunctor

/-! ## UncurryHom（旧 SerrePositivity/DifferentialGraded/Bimodule/UncurryHom.lean） -/

/-! # bimoduleからtensor積dg圏上のHom射を構成する -/

@[expose] public section UncurryHom

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory MonoidalCategory Opposite CochainComplex HomComplex HomologicalComplex
variable {A : Type u} [CommRing A] {B : Type v} {C : Type w}
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- tensor積のHomを、右作用、左作用の豊穣順合成へ送る。 -/
def uncurryHom (M : Bimodule A B C) (x y : DGTensorCategory A Bᵒᵖ C) :
    (x ⟶[Complex A] y) ⟶ homComplex A (M.value x.1.unop x.2) (M.value y.1.unop y.2) :=
  ((M.rightAt x.2).map x.1 y.1 ⊗ₘ (M.leftAt y.1.unop).map x.2 y.2) ≫
    enrichedComposition _ _ _

/-- 純粋Homでのuncurryingの成分式。豊穣順の符号を保持する。 -/
lemma uncurryHom_apply (M : Bimodule A B C) {x y : DGTensorCategory A Bᵒᵖ C} {p q n : ℤ}
    (f : GradedHom A x.1 y.1 p) (g : GradedHom A x.2 y.2 q) (hn : p + q = n) :
    (M.uncurryHom x y).f n (dgTensorElement A f g hn) =
      (p * q).negOnePow • (((M.rightAt x.2).map x.1 y.1).f p f).comp
        (M.leftCochain g y.1.unop) hn := by
  change (enrichedComposition _ _ _).f n
    ((((M.rightAt x.2).map x.1 y.1) ⊗ₘ ((M.leftAt y.1.unop).map x.2 y.2)).f n
      (ιTensorObj (x.1 ⟶[Complex A] y.1) (x.2 ⟶[Complex A] y.2) p q n hn (f ⊗ₜ[A] g))) = _
  rw [tensorMap_apply]
  exact enrichedComposition_apply _ _ _ p q n hn _ _

/-- 任意複体を対象と見た単位のcycleは通常恒等cochain。 -/
lemma complex_unitElement (P : Complex A) :
    (unitElement A P).val = Cochain.ofHom (𝟙 P) := by
  change (cycleFromUnit _ (identity P)).val = _
  rw [identity, cycleFromUnit_unitFromCycle]

lemma leftCochain_unit (M : Bimodule A B C) (b : B) (c : C) :
    M.leftCochain (unitElement A c).val b = Cochain.ofHom (𝟙 (M.value b c)) := by
  rw [leftCochain_eq]
  exact (DGFunctor.map_unitElement A (M.leftAt b) c).trans (complex_unitElement _)

/-- uncurryHomはtensor積の単位cycleを恒等cochainへ送る。 -/
lemma uncurryHom_unit (M : Bimodule A B C) (x : DGTensorCategory A Bᵒᵖ C) :
    (M.uncurryHom x x).f 0 (unitElement A x).val =
      Cochain.ofHom (𝟙 (M.value x.1.unop x.2)) := by
  rw [dgTensor_unitElement, uncurryHom_apply, leftCochain_unit]
  have h := DGFunctor.map_unitElement A (M.rightAt x.2).toFunctor x.1
  rw [complex_unitElement] at h
  have he := congrArg (fun f : Cochain (M.value x.1.unop x.2) (M.value x.1.unop x.2) 0 =>
    (0 * 0 : ℤ).negOnePow • f.comp (Cochain.ofHom (𝟙 (M.value x.1.unop x.2))) rfl) h
  exact he.trans (by simp)

/-- Hom射の単位cycle計算を、単位複体からの射の等式へ戻す。 -/
lemma uncurryHom_identity (M : Bimodule A B C) (x : DGTensorCategory A Bᵒᵖ C) :
    eId (Complex A) x ≫ M.uncurryHom x x = identity (M.value x.1.unop x.2) := by
  apply (unitCycleEquiv _).injective
  apply Subtype.ext
  change (cycleFromUnit _ (eId (Complex A) x ≫ M.uncurryHom x x)).val =
    (cycleFromUnit _ (identity (M.value x.1.unop x.2))).val
  rw [cycleFromUnit_postcomp, identity, cycleFromUnit_unitFromCycle]
  exact M.uncurryHom_unit x

end SerrePositivity.DifferentialGraded.Bimodule
end

end UncurryHom

/-! ## UncurryRestriction（旧 SerrePositivity/DifferentialGraded/Bimodule/UncurryRestriction.lean） -/

/-! # uncurryHomを因子へ制限した際の計算 -/

@[expose] public section UncurryRestriction

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory MonoidalCategory Opposite CochainComplex HomComplex HomologicalComplex
variable {A : Type u} [CommRing A] {B : Type v} {C : Type w}
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 第一因子に制限したuncurryHomは元の右作用。 -/
lemma uncurryHom_first (M : Bimodule A B C) (c : C) (x y : Bᵒᵖ) :
    dgTensorFirstHom A Bᵒᵖ C c x y ≫ M.uncurryHom (x, c) (y, c) =
      (M.rightAt c).map x y := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  have h := M.uncurryHom_apply (x := (x, c)) (y := (y, c)) f
    (unitElement A c).val (add_zero p)
  rw [leftCochain_unit] at h
  simp only [mul_zero, Int.negOnePow_zero, one_smul, Cochain.comp_id] at h
  exact (congrArg (fun t => (M.uncurryHom (x, c) (y, c)).f p t)
    (dgTensorFirstHom_apply A Bᵒᵖ C c x y p f)).trans h

/-- 第二因子に制限したuncurryHomは元の左作用。 -/
lemma uncurryHom_second (M : Bimodule A B C) (b : B) (c d : C) :
    dgTensorSecondHom A Bᵒᵖ C (op b) c d ≫ M.uncurryHom (op b, c) (op b, d) =
      (M.leftAt b).map c d := by
  apply HomologicalComplex.hom_ext
  intro q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro g
  have h := M.uncurryHom_apply (x := (op b, c)) (y := (op b, d))
    (unitElement A (op b)).val g (zero_add q)
  have hr := DGFunctor.map_unitElement A (M.rightAt c).toFunctor (op b)
  rw [complex_unitElement] at hr
  have he := congrArg (fun f : Cochain (M.value b c) (M.value b c) 0 =>
    f.comp (M.leftCochain g b) (zero_add q)) hr
  simp only [Cochain.id_comp] at he
  simp only [zero_mul, Int.negOnePow_zero, one_smul] at h
  exact (congrArg (fun t => (M.uncurryHom (op b, c) (op b, d)).f q t)
    (dgTensorSecondHom_apply A Bᵒᵖ C (op b) c d q g)).trans (h.trans he)

end SerrePositivity.DifferentialGraded.Bimodule
end

end UncurryRestriction

/-! ## CochainComposition（旧 SerrePositivity/DifferentialGraded/Bimodule/CochainComposition.lean） -/

/-! # bimoduleの両作用のcochain合成式 -/

@[expose] public section CochainComposition

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory Opposite CochainComplex HomComplex
variable {A : Type u} [CommRing A] {B : Type v} {C : Type w}
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

lemma rightCochain_forward (M : Bimodule A B C) (c : C) {x y z : Bᵒᵖ} {p q n : ℤ}
    (f : GradedHom A x y p) (g : GradedHom A y z q) (hn : p + q = n) :
    ((M.rightAt c).map x z).f n (forward A f g hn) =
      (p * q).negOnePow • (((M.rightAt c).map x y).f p f).comp
        (((M.rightAt c).map y z).f q g) hn :=
  DGFunctor.map_forward_cochain A (M.rightAt c).toFunctor f g hn

lemma leftCochain_forward (M : Bimodule A B C) (b : B) {x y z : C} {p q n : ℤ}
    (f : GradedHom A x y p) (g : GradedHom A y z q) (hn : p + q = n) :
    M.leftCochain (forward A f g hn) b =
      (p * q).negOnePow • (M.leftCochain f b).comp (M.leftCochain g b) hn :=
  DGFunctor.map_forward_cochain A (M.leftAt b) f g hn

end SerrePositivity.DifferentialGraded.Bimodule
end

end CochainComposition

/-! ## UncurryComposition（旧 SerrePositivity/DifferentialGraded/Bimodule/UncurryComposition.lean） -/

/-! # uncurryHomの純粋斉次tensor上の合成保存 -/

@[expose] public section UncurryComposition

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory MonoidalCategory Opposite CochainComplex HomComplex HomologicalComplex
variable {A : Type u} [CommRing A] {B : Type v} {C : Type w}
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

lemma uncurryHom_forward_pure (M : Bimodule A B C)
    {x y z : DGTensorCategory A Bᵒᵖ C} {p q r s n : ℤ}
    (f₁ : GradedHom A x.1 y.1 p) (f₂ : GradedHom A x.2 y.2 q)
    (g₁ : GradedHom A y.1 z.1 r) (g₂ : GradedHom A y.2 z.2 s)
    (hn : (p + q) + (r + s) = n) :
    (M.uncurryHom x z).f n
        (forward A (dgTensorElement A f₁ f₂ rfl) (dgTensorElement A g₁ g₂ rfl) hn) =
      ((p + q) * (r + s)).negOnePow •
        ((M.uncurryHom x y).f (p + q) (dgTensorElement A f₁ f₂ rfl)).comp
          ((M.uncurryHom y z).f (r + s) (dgTensorElement A g₁ g₂ rfl)) hn := by
  have hm (k : ℤˣ) (t : GradedHom A x z n) :
      (M.uncurryHom x z).f n (k • t) = k • (M.uncurryHom x z).f n t := by
    simp only [Units.smul_def, map_zsmul]
  have he := cochain_quad_interchange
    (((M.rightAt x.2).map x.1 y.1).f p f₁) (M.leftCochain f₂ y.1.unop)
    (((M.rightAt y.2).map y.1 z.1).f r g₁) (M.leftCochain g₂ z.1.unop)
    (((M.rightAt x.2).map y.1 z.1).f r g₁) (M.leftCochain f₂ z.1.unop)
    (M.interchange (b := z.1.unop) (b' := y.1.unop) (c := x.2) (c' := y.2) g₁ f₂)
    (by omega : p + q + r + s = n)
  rw [dgTensor_forward, hm, uncurryHom_apply, uncurryHom_apply, uncurryHom_apply,
    rightCochain_forward, leftCochain_forward]
  simp only [Cochain.units_smul_comp, Cochain.comp_units_smul, smul_smul]
  rw [he]
  simp only [smul_smul, mul_assoc]
  have hs : (q * r).negOnePow *
      (((p + r) * (q + s)).negOnePow * ((q * s).negOnePow * (p * r).negOnePow)) =
      ((p + q) * (r + s)).negOnePow *
        ((r * s).negOnePow * ((p * q).negOnePow * (q * r).negOnePow)) := by
    simp only [← Int.negOnePow_add]
    congr 1
    ring
  exact congrArg (fun k : ℤˣ => k • _) hs

/-- uncurryHomは全Hom複体で豊穣合成を保存する。 -/
lemma uncurryHom_comp (M : Bimodule A B C) (x y z : DGTensorCategory A Bᵒᵖ C) :
    eComp (Complex A) x y z ≫ M.uncurryHom x z =
      (M.uncurryHom x y ⊗ₘ M.uncurryHom y z) ≫
        enrichedComposition (M.value x.1.unop x.2) (M.value y.1.unop y.2)
          (M.value z.1.unop z.2) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply SerrePositivity.cochainTensorQuad_hom_ext
    (x.1 ⟶[Complex A] y.1) (x.2 ⟶[Complex A] y.2)
    (y.1 ⟶[Complex A] z.1) (y.2 ⟶[Complex A] z.2) n
  intro p q r s hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_fourfold'
  intro f₁ f₂ g₁ g₂
  change (M.uncurryHom x z).f n
      (forward A (dgTensorElement A f₁ f₂ rfl) (dgTensorElement A g₁ g₂ rfl) (by omega)) =
    (enrichedComposition _ _ _).f n
      ((M.uncurryHom x y ⊗ₘ M.uncurryHom y z).f n
        (ιTensorObj (x ⟶[Complex A] y) (y ⟶[Complex A] z) (p + q) (r + s) n (by omega)
          (dgTensorElement A f₁ f₂ rfl ⊗ₜ[A] dgTensorElement A g₁ g₂ rfl)))
  have hr := congrArg (fun t =>
    (enrichedComposition (M.value x.1.unop x.2) (M.value y.1.unop y.2)
      (M.value z.1.unop z.2)).f n t)
    (tensorMap_apply (M.uncurryHom x y) (M.uncurryHom y z) (p + q) (r + s) n (by omega)
      (dgTensorElement A f₁ f₂ rfl) (dgTensorElement A g₁ g₂ rfl))
  exact (M.uncurryHom_forward_pure f₁ f₂ g₁ g₂ (by omega)).trans
    (hr.trans (enrichedComposition_apply _ _ _ (p + q) (r + s) n (by omega) _ _)).symm

end SerrePositivity.DifferentialGraded.Bimodule
end

end UncurryComposition

/-! ## Uncurry（旧 SerrePositivity/DifferentialGraded/Bimodule/Uncurry.lean） -/

/-! # bimoduleの実際のuncurried dg関手 -/

@[expose] public section Uncurry

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory MonoidalCategory Opposite
variable {A : Type u} [CommRing A] {B : Type v} {C : Type w}
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 全Homで単位・合成を保存するtensor積dg圏上の関手。 -/
def toTensorFunctor (M : Bimodule A B C) : BimoduleTensorFunctor A B C where
  obj x := M.value x.1.unop x.2
  map := M.uncurryHom
  map_id := M.uncurryHom_identity
  map_comp := M.uncurryHom_comp

lemma toTensorFunctor_rightAt (M : Bimodule A B C) (c : C) :
    M.toTensorFunctor.rightAt c = M.rightAt c := by
  apply EnrichedFunctor.ext (Complex A)
    (F := (M.toTensorFunctor.rightAt c).toFunctor) (G := (M.rightAt c).toFunctor) (fun _ => rfl)
  intro x y
  change (dgTensorFirstHom A Bᵒᵖ C c x y ≫ M.uncurryHom (x, c) (y, c)) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  exact M.uncurryHom_first c x y

lemma toTensorFunctor_leftAt (M : Bimodule A B C) (b : B) :
    M.toTensorFunctor.leftAt b = M.leftAt b := by
  apply EnrichedFunctor.ext (Complex A)
    (F := M.toTensorFunctor.leftAt b) (G := M.leftAt b) (fun _ => rfl)
  intro c d
  change (dgTensorSecondHom A Bᵒᵖ C (op b) c d ≫
    M.uncurryHom (op b, c) (op b, d)) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  exact M.uncurryHom_second b c d

end SerrePositivity.DifferentialGraded.Bimodule
end

end Uncurry

/-! ## TensorComparison（旧 SerrePositivity/DifferentialGraded/Bimodule/TensorComparison.lean） -/

/-! # bimoduleとtensor積dg圏上の関手の比較 -/

@[expose] public section TensorComparison

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite CochainComplex HomComplex HomologicalComplex
variable {A : Type u} [CommRing A] {B : Type v} {C : Type w}
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

namespace BimoduleTensorFunctor
lemma toBimodule_rightAt (F : BimoduleTensorFunctor A B C) (c : C) :
    F.toBimodule.rightAt c = F.rightAt c := rfl

lemma toBimodule_leftAt (F : BimoduleTensorFunctor A B C) (b : B) :
    F.toBimodule.leftAt b = F.leftAt b := by
  apply EnrichedFunctor.ext (Complex A)
    (F := F.toBimodule.leftAt b) (G := F.leftAt b) (fun _ => rfl)
  intro c d
  change (F.toBimodule.toFunctor.map c d ≫
    moduleHomπ A B (F.rightAt c) (F.rightAt d) b) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  exact F.toBimodule_map_π c d b

omit [Small.{u} B] in
/-- 純粋tensorの像は制限された二作用の豊穣順合成。 -/
lemma map_tensorElement (F : BimoduleTensorFunctor A B C)
    {x y : DGTensorCategory A Bᵒᵖ C} {p q n : ℤ}
    (f : GradedHom A x.1 y.1 p) (g : GradedHom A x.2 y.2 q) (hn : p + q = n) :
    (F.map x y).f n (dgTensorElement A f g hn) =
      (p * q).negOnePow • (((F.rightAt x.2).map x.1 y.1).f p f).comp
        (((F.leftAt y.1.unop).map x.2 y.2).f q g) hn := by
  have h := DGFunctor.map_forward_cochain A F (x := x) (y := (y.1, x.2)) (z := y)
    ((dgTensorFirstHom A Bᵒᵖ C x.2 x.1 y.1).f p f)
    ((dgTensorSecondHom A Bᵒᵖ C y.1 x.2 y.2).f q g) hn
  rw [dgTensor_first_then_second] at h
  exact h
end BimoduleTensorFunctor

namespace Bimodule
lemma toTensorFunctor_toBimodule (M : Bimodule A B C) :
    M.toTensorFunctor.toBimodule = M := by
  apply ext_rightAt_leftAt
  · intro c
    exact (M.toTensorFunctor.toBimodule_rightAt c).trans (M.toTensorFunctor_rightAt c)
  · intro b
    exact (M.toTensorFunctor.toBimodule_leftAt b).trans (M.toTensorFunctor_leftAt b)
end Bimodule

namespace BimoduleTensorFunctor
lemma toBimodule_toTensorFunctor (F : BimoduleTensorFunctor A B C) :
    F.toBimodule.toTensorFunctor = F := by
  apply EnrichedFunctor.ext (Complex A)
    (F := F.toBimodule.toTensorFunctor) (G := F) (fun _ => rfl)
  intro x y
  change F.toBimodule.uncurryHom x y ≫ 𝟙 _ = F.map x y
  rw [Category.comp_id]
  apply tensorHom_ext
  intro p q n hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f g
  change (F.toBimodule.uncurryHom x y).f n (dgTensorElement A f g hn) =
    (F.map x y).f n (dgTensorElement A f g hn)
  have hl := congrArg (fun t => t.f q g) (F.toBimodule_map_π x.2 y.2 y.1.unop)
  change F.toBimodule.leftCochain g y.1.unop = ((F.leftAt y.1.unop).map x.2 y.2).f q g at hl
  have he := congrArg (fun t : Cochain (F.obj (y.1, x.2)) (F.obj y) q =>
    (p * q).negOnePow • (((F.rightAt x.2).map x.1 y.1).f p f).comp t hn) hl
  exact (F.toBimodule.uncurryHom_apply f g hn).trans
    (he.trans (F.map_tensorElement f g hn).symm)
end BimoduleTensorFunctor

variable (A B C)
/-- curried全Hom end表示とtensor積dg圏上の豊穣関手表示の対象データの同値。 -/
def bimoduleEquivTensorFunctor : Bimodule A B C ≃ BimoduleTensorFunctor A B C where
  toFun := Bimodule.toTensorFunctor
  invFun := BimoduleTensorFunctor.toBimodule
  left_inv := Bimodule.toTensorFunctor_toBimodule
  right_inv := BimoduleTensorFunctor.toBimodule_toTensorFunctor

end SerrePositivity.DifferentialGraded
end

end TensorComparison

/-! ## TensorModuleMaps（旧 SerrePositivity/DifferentialGraded/Bimodule/TensorModuleMaps.lean） -/

/-! # 積dg圏上の左加群射を全Hom自然なbimodule射へ制限する

## 概要
積dg圏上の左加群射を全Hom自然なbimodule射へ制限する。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Bimodule/TensorModuleFunctor.lean。局所導来合成の計算部品、
一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section TensorModuleMaps

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

/-- 既存の全Hom endを持つ、Bᵒᵖ⊗C上の左dg加群の閉零圏。 -/
abbrev BimoduleTensorModuleCategory := LeftModuleCategory A (DGTensorCategory A Bᵒᵖ C)

namespace BimoduleTensorModule

abbrev underlying (M : BimoduleTensorModuleCategory A B C) : BimoduleTensorFunctor A B C :=
  ForgetEnrichment.to (Complex A) M

def rightMap {M N : BimoduleTensorModuleCategory A B C} (f : M ⟶ N) (c : C) :
    ForgetEnrichment.of (Complex A) ((underlying A B C M).rightAt c) ⟶
      ForgetEnrichment.of (Complex A) ((underlying A B C N).rightAt c) :=
  moduleMorphismMk A B
    (M := (underlying A B C M).rightAt c) (N := (underlying A B C N).rightAt c)
    (fun b => (leftModuleEvaluation A (DGTensorCategory A Bᵒᵖ C) (b, c)).map f)
    (fun x y => by
      have h := congrArg (fun z => dgTensorFirstHom A Bᵒᵖ C c x y ≫ z)
        (leftModuleMorphism_naturality A (DGTensorCategory A Bᵒᵖ C) f (x, c) (y, c))
      exact (Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm))

@[simp]
lemma rightMap_component {M N : BimoduleTensorModuleCategory A B C} (f : M ⟶ N) (b : B) (c : C) :
    moduleMorphismComponent A B ((underlying A B C M).rightAt c)
      ((underlying A B C N).rightAt c) (rightMap A B C f c) b =
    (leftModuleEvaluation A (DGTensorCategory A Bᵒᵖ C) (op b, c)).map f :=
  moduleMorphismMk_eval A B _ _ b

lemma rightMap_left_naturality {M N : BimoduleTensorModuleCategory A B C} (f : M ⟶ N)
    (c c' : C) :
    (underlying A B C M).toBimodule.toFunctor.map c c' ≫
      moduleHomPostcompose A B ((underlying A B C M).rightAt c)
        ((underlying A B C M).rightAt c') ((underlying A B C N).rightAt c') (rightMap A B C f c') =
    (underlying A B C N).toBimodule.toFunctor.map c c' ≫
      moduleHomPrecompose A B ((underlying A B C M).rightAt c)
        ((underlying A B C N).rightAt c) ((underlying A B C N).rightAt c') (rightMap A B C f c) :=
      by
  apply moduleHom_ext
  intro b
  simp only [Category.assoc]
  rw [moduleHomPostcompose_π, moduleHomPrecompose_π]
  rw [rightMap_component, rightMap_component]
  have h := congrArg (fun z => dgTensorSecondHom A Bᵒᵖ C (op b) c c' ≫ z)
    (leftModuleMorphism_naturality A (DGTensorCategory A Bᵒᵖ C) f (op b, c) (op b, c'))
  have hn : ((underlying A B C M).leftAt b).map c c' ≫
      homPostcompose ((underlying A B C M).obj (op b, c))
        ((leftModuleEvaluation A (DGTensorCategory A Bᵒᵖ C) (op b, c')).map f) =
    ((underlying A B C N).leftAt b).map c c' ≫
      homPrecompose ((leftModuleEvaluation A (DGTensorCategory A Bᵒᵖ C) (op b, c)).map f)
        ((underlying A B C N).obj (op b, c')) :=
    (Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)
  have hL := congrArg (fun k : (c ⟶[Complex A] c') ⟶
      homComplex A ((underlying A B C M).obj (op b, c))
        ((underlying A B C M).obj (op b, c')) =>
    k ≫ homPostcompose ((underlying A B C M).obj (op b, c))
      ((leftModuleEvaluation A (DGTensorCategory A Bᵒᵖ C) (op b, c')).map f))
    (BimoduleTensorFunctor.toBimodule_map_π (underlying A B C M) c c' b)
  have hR := congrArg (fun k : (c ⟶[Complex A] c') ⟶
      homComplex A ((underlying A B C N).obj (op b, c))
        ((underlying A B C N).obj (op b, c')) =>
    k ≫ homPrecompose ((leftModuleEvaluation A (DGTensorCategory A Bᵒᵖ C) (op b, c)).map f)
      ((underlying A B C N).obj (op b, c')))
    (BimoduleTensorFunctor.toBimodule_map_π (underlying A B C N) c c' b)
  exact (Category.assoc _ _ _).symm.trans
    (hL.trans (hn.trans (hR.symm.trans (Category.assoc _ _ _))))

end BimoduleTensorModule
end SerrePositivity.DifferentialGraded
end

end TensorModuleMaps

/-! ## TensorModuleFunctor（旧 SerrePositivity/DifferentialGraded/Bimodule/TensorModuleFunctor.lean） -/

/-! # 積dg圏上の加群から主bimodule圏への射・評価を保つ関手

## 概要
積dg圏上の加群から主bimodule圏への射・評価を保つ関手。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Bimodule/TensorModuleComparison.lean。局所導来合成の計算部品、
一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section TensorModuleFunctor

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensorModule
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

def map {M N : BimoduleTensorModuleCategory A B C} (f : M ⟶ N) :
    BimoduleCategory.of A B C (underlying A B C M).toBimodule ⟶
      BimoduleCategory.of A B C (underlying A B C N).toBimodule :=
  ⟨rightMap A B C f, rightMap_left_naturality A B C f⟩

@[simp]
lemma map_value {M N : BimoduleTensorModuleCategory A B C} (f : M ⟶ N) (b : B) (c : C) :
    (BimoduleCategory.valueEvaluation A B C b c).map (map A B C f) =
      (leftModuleEvaluation A (DGTensorCategory A Bᵒᵖ C) (op b, c)).map f :=
  rightMap_component A B C f b c

lemma map_id (M : BimoduleTensorModuleCategory A B C) :
    map A B C (𝟙 M) = 𝟙 (BimoduleCategory.of A B C (underlying A B C M).toBimodule) := by
  apply BimoduleCategory.value_hom_ext A B C
  intro b c
  rw [map_value, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rfl

lemma map_comp {M N P : BimoduleTensorModuleCategory A B C} (f : M ⟶ N) (g : N ⟶ P) :
    map A B C (f ≫ g) = map A B C f ≫ map A B C g := by
  apply BimoduleCategory.value_hom_ext A B C
  intro b c
  rw [map_value, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    map_value, map_value]

/-- 射が両作用に全Hom自然であることを保持した、実際の閉零圏間の関手。 -/
def functor : BimoduleTensorModuleCategory A B C ⥤ BimoduleCategory A B C where
  obj M := BimoduleCategory.of A B C (underlying A B C M).toBimodule
  map := map A B C
  map_id := map_id A B C
  map_comp := map_comp A B C

@[simp]
lemma functor_map_value {M N : BimoduleTensorModuleCategory A B C} (f : M ⟶ N) (b : B) (c : C) :
    (BimoduleCategory.valueEvaluation A B C b c).map ((functor A B C).map f) =
      (leftModuleEvaluation A (DGTensorCategory A Bᵒᵖ C) (op b, c)).map f := map_value A B C f b c

/-- 各対象での複体の評価は、積dg圏上の元の評価に自然同型として一致する。 -/
def evaluationIso (b : B) (c : C) :
    functor A B C ⋙ BimoduleCategory.valueEvaluation A B C b c ≅
      leftModuleEvaluation A (DGTensorCategory A Bᵒᵖ C) (op b, c) :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (fun f => by
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      exact map_value A B C f b c)

instance faithful : (functor A B C).Faithful where
  map_injective {M N} {f g} h := by
    apply leftModuleMorphism_ext A (DGTensorCategory A Bᵒᵖ C)
    intro x
    rcases x with ⟨b, c⟩
    have hh := congrArg (fun a => (BimoduleCategory.valueEvaluation A B C b.unop c).map a) h
    rw [functor_map_value, functor_map_value] at hh
    exact hh

end SerrePositivity.DifferentialGraded.BimoduleTensorModule
end

end TensorModuleFunctor

/-! ## TensorModuleComparison（旧 SerrePositivity/DifferentialGraded/Bimodule/TensorModuleComparison.lean） -/

/-! # 積dg圏上の加群比較の本質的全射性と準同型の保存・反映

## 概要
積dg圏上の加群比較の本質的全射性と準同型の保存・反映。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Bimodule/TensorModuleFull.lean。局所導来合成の計算部品、一般Morita・
相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section TensorModuleComparison

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensorModule
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

def objectPreimage (M : BimoduleCategory A B C) : BimoduleTensorModuleCategory A B C :=
  ForgetEnrichment.of (Complex A) (BimoduleCategory.underlying A B C M).toTensorFunctor

def objectPreimageIso (M : BimoduleCategory A B C) :
    (functor A B C).obj (objectPreimage A B C M) ≅ M :=
  eqToIso (by
    exact congrArg (BimoduleCategory.of A B C)
      (Bimodule.toTensorFunctor_toBimodule (BimoduleCategory.underlying A B C M)))

instance essSurj : (functor A B C).EssSurj where
  mem_essImage M := ⟨objectPreimage A B C M, ⟨objectPreimageIso A B C M⟩⟩

/-- 元の二つの閉零圏で指定した準同型のクラスは、値の評価により一致する。 -/
lemma functor_quasiIso_iff {M N : BimoduleTensorModuleCategory A B C} (f : M ⟶ N) :
    BimoduleCategory.quasiIso A B C ((functor A B C).map f) ↔
      leftModuleQuasiIso A (DGTensorCategory A Bᵒᵖ C) f := by
  constructor
  · intro hf
    apply (leftModuleQuasiIso_iff A (DGTensorCategory A Bᵒᵖ C) f).2
    intro x
    rcases x with ⟨b, c⟩
    have hh := hf b.unop c
    rw [functor_map_value] at hh
    exact hh
  · intro hf b c
    rw [functor_map_value]
    exact (leftModuleQuasiIso_iff A (DGTensorCategory A Bᵒᵖ C) f).1 hf (op b, c)

end SerrePositivity.DifferentialGraded.BimoduleTensorModule
end

end TensorModuleComparison
