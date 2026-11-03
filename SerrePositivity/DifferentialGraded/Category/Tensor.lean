module

public import SerrePositivity.DifferentialGraded.Module.Basic
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
public import SerrePositivity.DifferentialGraded.Category.Basic
public import SerrePositivity.DifferentialGraded.Module.TensorFree
public import SerrePositivity.DifferentialGraded.Complexes.HomLimits
public import Mathlib.Algebra.Homology.HomotopyCategory

/-!
# Category.Tensor

## 概要
13 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## Tensor（旧 SerrePositivity/DifferentialGraded/Category/Tensor.lean） -/

/-! # 二つのdg圏のtensor積

Homの組の豊穣を、Mathlibのtensorモノイダル関手でtransportする。
合成の交差は同関手のtensorμであり、独自の圏構造を増やさない。
-/

@[expose] public section Tensor
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C]

/-- 同じHom宇宙の複体の積に、既存の積monoidal構造を指定する。 -/
instance complexPairMonoidal : MonoidalCategory (Complex A × Complex A) :=
  MonoidalCategory.prodMonoidal (Complex A) (Complex A)

/-- Homを組として保持する積基底上の豊穣構造。 -/
instance dgPairEnrichment : EnrichedCategory (Complex A × Complex A) (B × C) where
  Hom x y := (x.1 ⟶[Complex A] y.1, x.2 ⟶[Complex A] y.2)
  id x := ⟨eId (Complex A) x.1, eId (Complex A) x.2⟩
  comp x y z := ⟨eComp (Complex A) x.1 y.1 z.1, eComp (Complex A) x.2 y.2 z.2⟩
  id_comp x y := Prod.ext (e_id_comp (Complex A) x.1 y.1) (e_id_comp (Complex A) x.2 y.2)
  comp_id x y := Prod.ext (e_comp_id (Complex A) x.1 y.1) (e_comp_id (Complex A) x.2 y.2)
  assoc x y z t := Prod.ext (e_assoc (Complex A) x.1 y.1 z.1 t.1)
    (e_assoc (Complex A) x.2 y.2 z.2 t.2)

/-- dg圏のtensor積。対象は組、HomはHom複体のtensor積。 -/
abbrev DGTensorCategory := TransportEnrichment (tensor (Complex A)) (B × C)

@[instance_reducible]
def dgTensorEnrichment : DGCategory A (DGTensorCategory A B C) := inferInstance

lemma dgTensor_hom (x y : DGTensorCategory A B C) :
    (x ⟶[Complex A] y) = (x.1 ⟶[Complex A] y.1) ⊗ (x.2 ⟶[Complex A] y.2) := rfl

/-- tensor積の単位は二つの閉単位のtensorから得る。 -/
lemma dgTensor_identity (x : DGTensorCategory A B C) :
    eId (Complex A) x = (λ_ (𝟙_ (Complex A))).inv ≫
      (eId (Complex A) x.1 ⊗ₘ eId (Complex A) x.2) := by
  rw [TransportEnrichment.eId_eq, tensor_ε]
  rfl

/-- 豊穣合成では中央二因子のsigned braidingを使う。 -/
lemma dgTensor_composition (x y z : DGTensorCategory A B C) :
    eComp (Complex A) x y z =
      tensorμ (x.1 ⟶[Complex A] y.1) (x.2 ⟶[Complex A] y.2)
        (y.1 ⟶[Complex A] z.1) (y.2 ⟶[Complex A] z.2) ≫
      (eComp (Complex A) x.1 y.1 z.1 ⊗ₘ eComp (Complex A) x.2 y.2 z.2) := by
  rw [TransportEnrichment.eComp_eq, tensor_μ]
  rfl

end SerrePositivity.DifferentialGraded
end

end Tensor

/-! ## TensorSmall（旧 SerrePositivity/DifferentialGraded/Category/TensorSmall.lean） -/

/-! # 小さい二つのdg圏のtensor積の対象のsmall性

## 概要
小さい二つのdg圏のtensor積の対象のsmall性。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Bimodule/TensorModuleMaps.lean。dg加群の導来作用・準同値比較の基盤。
任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section TensorSmall
universe u v w

namespace SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

instance dgTensorSmall : Small.{u} (DGTensorCategory A B C) :=
  inferInstanceAs (Small.{u} (B × C))

end SerrePositivity.DifferentialGraded

end TensorSmall

/-! ## TensorElements（旧 SerrePositivity/DifferentialGraded/Category/TensorElements.lean） -/

/-! # tensor積dg圏の純粋斉次Homと合成の交差符号 -/

@[expose] public section TensorElements
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] {B : Type v} {C : Type w}
  [DGCategory A B] [DGCategory A C]

/-- 二つの斉次Homからtensor積dg圏の斉次Homを作る。 -/
def dgTensorElement {x y : DGTensorCategory A B C} {p q n : ℤ}
    (f : GradedHom A x.1 y.1 p) (g : GradedHom A x.2 y.2 q) (hn : p + q = n) :
    GradedHom A x y n :=
  ιTensorObj (x.1 ⟶[Complex A] y.1) (x.2 ⟶[Complex A] y.2) p q n hn (f ⊗ₜ[A] g)

/-- 豊穣順合成の交差符号は最初の第二因子と次の第一因子の次数積。 -/
lemma dgTensor_forward {x y z : DGTensorCategory A B C} {p q r s n : ℤ}
    (f₁ : GradedHom A x.1 y.1 p) (f₂ : GradedHom A x.2 y.2 q)
    (g₁ : GradedHom A y.1 z.1 r) (g₂ : GradedHom A y.2 z.2 s)
    (hn : (p + q) + (r + s) = n) :
    forward A (dgTensorElement A f₁ f₂ rfl) (dgTensorElement A g₁ g₂ rfl) hn =
      (q * r).negOnePow • dgTensorElement A
        (forward A f₁ g₁ rfl) (forward A f₂ g₂ rfl) (by omega) := by
  unfold forward dgTensorElement
  rw [dgTensor_composition]
  change (eComp (Complex A) x.1 y.1 z.1 ⊗ₘ eComp (Complex A) x.2 y.2 z.2).f n
    ((tensorμ (x.1 ⟶[Complex A] y.1) (x.2 ⟶[Complex A] y.2)
      (y.1 ⟶[Complex A] z.1) (y.2 ⟶[Complex A] z.2)).f n
      (SerrePositivity.cochainTensorQuadι _ _ _ _ p q r s n (by omega)
        ((f₁ ⊗ₜ[A] f₂) ⊗ₜ[A] (g₁ ⊗ₜ[A] g₂)))) = _
  rw [tensorμ_apply]
  simp only [Units.smul_def, map_zsmul]
  rw [SerrePositivity.cochainTensorQuadι_apply]
  exact congrArg (fun t : (x ⟶[Complex A] z).X n => ((q * r).negOnePow : ℤ) • t)
    (tensorMap_apply (eComp (Complex A) x.1 y.1 z.1) (eComp (Complex A) x.2 y.2 z.2)
      (p + r) (q + s) n (by omega)
      (ιTensorObj (x.1 ⟶[Complex A] y.1) (y.1 ⟶[Complex A] z.1) p r (p + r) rfl (f₁ ⊗ₜ[A] g₁))
      (ιTensorObj (x.2 ⟶[Complex A] y.2) (y.2 ⟶[Complex A] z.2) q s (q + s) rfl (f₂ ⊗ₜ[A] g₂)))

end SerrePositivity.DifferentialGraded
end

end TensorElements

/-! ## TensorReindex（旧 SerrePositivity/DifferentialGraded/Category/TensorReindex.lean） -/

/-! # 中間の和次数を指定したtensor積の合成公式 -/

@[expose] public section TensorReindex
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] {B : Type v} {C : Type w}
  [DGCategory A B] [DGCategory A C]

/-- 各因子と全体の中間次数を別々に指定して合成する。 -/
lemma dgTensor_forward_of_sum {x y z : DGTensorCategory A B C} {p q r s a b c d n : ℤ}
    (f₁ : GradedHom A x.1 y.1 p) (f₂ : GradedHom A x.2 y.2 q)
    (g₁ : GradedHom A y.1 z.1 r) (g₂ : GradedHom A y.2 z.2 s)
    (ha : p + q = a) (hb : r + s = b) (hc : p + r = c) (hd : q + s = d)
    (hn : a + b = n) :
    forward A (dgTensorElement A f₁ f₂ ha) (dgTensorElement A g₁ g₂ hb) hn =
      (q * r).negOnePow • dgTensorElement A
        (forward A f₁ g₁ hc) (forward A f₂ g₂ hd) (by omega) := by
  subst a b c d
  exact dgTensor_forward A f₁ f₂ g₁ g₂ hn

end SerrePositivity.DifferentialGraded
end

end TensorReindex

/-! ## TensorComposition（旧 SerrePositivity/DifferentialGraded/Category/TensorComposition.lean） -/

/-! # tensor積dg圏の通常順合成の符号 -/

@[expose] public section TensorComposition
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] {B : Type v} {C : Type w}
  [DGCategory A B] [DGCategory A C]

lemma dgTensorElement_units_smul {x y : DGTensorCategory A B C} {p q n : ℤ}
    (f : GradedHom A x.1 y.1 p) (g : GradedHom A x.2 y.2 q) (hn : p + q = n)
    (a b : ℤˣ) :
    dgTensorElement A (a • f) (b • g) hn = (a * b) • dgTensorElement A f g hn := by
  simp only [dgTensorElement, Units.smul_def, ← TensorProduct.smul_tmul',
    TensorProduct.tmul_smul, map_zsmul, smul_smul, Units.val_mul, mul_comm]

/-- 通常順合成の交差符号は最初の第一因子と次の第二因子の次数積。 -/
lemma dgTensor_compose {x y z : DGTensorCategory A B C} {p q r s n : ℤ}
    (f₁ : GradedHom A x.1 y.1 p) (f₂ : GradedHom A x.2 y.2 q)
    (g₁ : GradedHom A y.1 z.1 r) (g₂ : GradedHom A y.2 z.2 s)
    (hn : (p + q) + (r + s) = n) :
    compose A (dgTensorElement A g₁ g₂ rfl) (dgTensorElement A f₁ f₂ rfl) hn =
      (p * s).negOnePow • dgTensorElement A
        (compose A g₁ f₁ rfl) (compose A g₂ f₂ rfl) (by omega) := by
  have hs : ((p + q) * (r + s)).negOnePow * (q * r).negOnePow =
      (p * s).negOnePow * ((p * r).negOnePow * (q * s).negOnePow) := by
    simp only [← Int.negOnePow_add]
    have he : (p + q) * (r + s) + q * r = p * s + (p * r + q * s) + 2 * (q * r) := by ring
    rw [he, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]
  simp only [compose, dgTensor_forward, dgTensorElement_units_smul, smul_smul]
  rw [hs]

end SerrePositivity.DifferentialGraded
end

end TensorComposition

/-! ## Induced（旧 SerrePositivity/DifferentialGraded/Category/Induced.lean） -/

/-!
概要：任意のラベル族へ全 Hom 複体を引き戻した dg 圏と評価を構成する。
方針：単位・合成を元の dg 圏からそのまま使い、評価の Hom 作用を恒等にする。
規約：対象値の単射性・Small 性・充満部分集合への置換を必要としない。
使われ方：ラベルを保持する自由表示・cone・反復表示模型の全次数評価。
-/

@[expose] public section Induced
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]
  {I : Type w} (value : I → D)

@[instance_reducible] def inducedDGCategory : DGCategory A I :=
  ofHomObjects A I (fun x y => homObject A D (value x) (value y))
    (fun x => eId (Complex A) (value x))
    (fun x y z => eComp (Complex A) (value x) (value y) (value z))
    (fun x y => EnrichedCategory.id_comp (value x) (value y))
    (fun x y => EnrichedCategory.comp_id (value x) (value y))
    (fun w x y z => EnrichedCategory.assoc (value w) (value x) (value y) (value z))

def inducedDGEvaluation :
    letI := inducedDGCategory A value
    DGFunctor A I D := by
  letI := inducedDGCategory A value
  exact { obj := value
          map := fun _ _ => 𝟙 _
          map_id := fun _ => by simp; rfl
          map_comp := fun _ _ _ => by simp; rfl }

lemma inducedDGEvaluation_homIso (x y : I) :
    letI := inducedDGCategory A value
    IsIso ((inducedDGEvaluation A value).map x y) := by
  change IsIso (𝟙 _)
  infer_instance

end SerrePositivity.DifferentialGraded
end

end Induced

/-! ## FullSubcategory（旧 SerrePositivity/DifferentialGraded/Category/FullSubcategory.lean） -/

/-! # 主dg圏の充満dg部分圏

Hom複体・微分・豊穣合成をそのまま制限する。閉零射とH⁰の両方で包含は完全忠実。
-/

@[expose] public section FullSubcategory
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (P : D → Prop)

/-- 対象の性質Pで制限した充満dg部分圏の対象型。対象宇宙は元のDから継承する。 -/
abbrev DGFullSubcategory := {x : D // P x}

/-- Hom複体・単位・合成を元の豊穣圏から制限し、その法則を継承する。 -/
instance dgFullSubcategoryEnrichment : DGCategory A (DGFullSubcategory D P) :=
  ofHomObjects A _ (fun x y => homObject A D x.val y.val)
    (fun x => eId (Complex A) x.val) (fun x y z => eComp (Complex A) x.val y.val z.val)
    (fun x y => EnrichedCategory.id_comp x.val y.val)
    (fun x y => EnrichedCategory.comp_id x.val y.val)
    (fun w x y z => EnrichedCategory.assoc w.val x.val y.val z.val)

/-- 充満dg部分圏の包含。各Hom複体上では恒等射である。 -/
def dgFullSubcategoryInclusion : DGFunctor A (DGFullSubcategory D P) D where
  obj x := x.val
  map _ _ := 𝟙 _
  map_id _ := by simp; rfl
  map_comp _ _ _ := by simp; rfl

/-- 包含は閉零射で充満。元と同じHom複体なので射をそのまま持ち上げる。 -/
instance dgFullSubcategoryInclusionClosedFull :
    (dgFullSubcategoryInclusion A D P).onClosed.Full where
  map_surjective {x y} f := by
    change ∃ g : 𝟙_ (Complex A) ⟶ homObject A D x.val y.val, g ≫ 𝟙 _ = f
    exact ⟨f, Category.comp_id _⟩

/-- 包含は閉零射で忠実。Hom複体上の恒等射との合成を消去する。 -/
instance dgFullSubcategoryInclusionClosedFaithful :
    (dgFullSubcategoryInclusion A D P).onClosed.Faithful where
  map_injective {x y} f g h := by
    let X : DGFullSubcategory D P := ForgetEnrichment.to (Complex A) x
    let Y : DGFullSubcategory D P := ForgetEnrichment.to (Complex A) y
    let f' : 𝟙_ (Complex A) ⟶ homObject A D X.val Y.val :=
      ForgetEnrichment.homTo (Complex A) f
    let g' : 𝟙_ (Complex A) ⟶ homObject A D X.val Y.val :=
      ForgetEnrichment.homTo (Complex A) g
    have h' : f' ≫ 𝟙 _ = g' ≫ 𝟙 _ := h
    have he : f' = g' := by simpa only [Category.comp_id] using h'
    exact he

/-- 包含は境界関係を反映する。同じHom複体上のホモトピーを使用する。 -/
lemma dgFullSubcategoryInclusion_boundary_iff {x y : ClosedCategory A (DGFullSubcategory D P)}
    (f g : x ⟶ y) :
    boundaryRelation A D ((dgFullSubcategoryInclusion A D P).onClosed.map f)
      ((dgFullSubcategoryInclusion A D P).onClosed.map g) ↔
        boundaryRelation A (DGFullSubcategory D P) f g := by
  change Nonempty (Homotopy (ForgetEnrichment.homTo (Complex A) f ≫ 𝟙 _)
    (ForgetEnrichment.homTo (Complex A) g ≫ 𝟙 _)) ↔
    Nonempty (Homotopy (ForgetEnrichment.homTo (Complex A) f)
      (ForgetEnrichment.homTo (Complex A) g))
  simp only [Category.comp_id]

/-- H⁰包含の射計算は閉零包含の商への像と一致する。 -/
lemma dgFullSubcategoryInclusion_onHomotopy_map
    {x y : ClosedCategory A (DGFullSubcategory D P)} (f : x ⟶ y) :
    (dgFullSubcategoryInclusion A D P).onHomotopy.map
        ((toHomotopy A (DGFullSubcategory D P)).map f) =
      (toHomotopy A D).map ((dgFullSubcategoryInclusion A D P).onClosed.map f) := rfl

/-- H⁰包含は充満。閉零射への商の全射性と閉零包含の充満性を使う。 -/
instance dgFullSubcategoryInclusionHomotopyFull :
    (dgFullSubcategoryInclusion A D P).onHomotopy.Full where
  map_surjective {x y} f := by
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    obtain ⟨f, rfl⟩ := (toHomotopy A D).map_surjective f
    obtain ⟨g, rfl⟩ := (dgFullSubcategoryInclusion A D P).onClosed.map_surjective f
    exact ⟨(toHomotopy A (DGFullSubcategory D P)).map g,
      dgFullSubcategoryInclusion_onHomotopy_map A D P g⟩

/-- H⁰包含は忠実。閉零代表で境界関係の反映に帰着する。 -/
instance dgFullSubcategoryInclusionHomotopyFaithful :
    (dgFullSubcategoryInclusion A D P).onHomotopy.Faithful where
  map_injective {x y} f g h := by
    obtain ⟨f, rfl⟩ := (toHomotopy A (DGFullSubcategory D P)).map_surjective f
    obtain ⟨g, rfl⟩ := (toHomotopy A (DGFullSubcategory D P)).map_surjective g
    rw [dgFullSubcategoryInclusion_onHomotopy_map,
      dgFullSubcategoryInclusion_onHomotopy_map] at h
    exact (toHomotopy_map_eq_iff A (DGFullSubcategory D P) f g).mpr
      ((dgFullSubcategoryInclusion_boundary_iff A D P f g).mp
        ((toHomotopy_map_eq_iff A D _ _).mp h))

end SerrePositivity.DifferentialGraded
end

end FullSubcategory

/-! ## Restriction（旧 SerrePositivity/DifferentialGraded/Category/Restriction.lean） -/

/-! # 対象の性質を保つdg関手の充満部分圏への制限 -/

@[expose] public section Restriction
universe u v w

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {A : Type u} [CommRing A] {D : Type v} {E : Type w}
  [DGCategory A D] [DGCategory A E]

/-- 対象の性質を保つdg関手を充満dg部分圏へ制限する。全Hom射は元の関手と同じである。 -/
def DGFunctor.restrict (F : DGFunctor A D E) (P : D → Prop) (Q : E → Prop)
    (h : ∀ X, P X → Q (F.obj X)) : DGFunctor A (DGFullSubcategory D P) (DGFullSubcategory E Q) where
  obj X := ⟨F.obj X.val, h X.val X.property⟩
  map X Y := F.map X.val Y.val
  map_id X := F.map_id X.val
  map_comp X Y Z := F.map_comp X.val Y.val Z.val

/-- 制限と包含の可換性。抽象的な対象型で証明し、具体的な大きいHom構成を展開しない。 -/
lemma DGFunctor.restrict_comp_inclusion (F : DGFunctor A D E) (P : D → Prop) (Q : E → Prop)
    (h : ∀ X, P X → Q (F.obj X)) :
    DGFunctor.comp (F.restrict P Q h) (dgFullSubcategoryInclusion A E Q) =
      DGFunctor.comp (dgFullSubcategoryInclusion A D P) F := by
  dsimp only [DGFunctor.comp, EnrichedFunctor.comp, DGFunctor.restrict, dgFullSubcategoryInclusion]
  congr 1

end SerrePositivity.DifferentialGraded
end

end Restriction

/-! ## RestrictionComparison（旧 SerrePositivity/DifferentialGraded/Category/RestrictionComparison.lean） -/

/-! # 充満dg部分圏の関手制限に対するH⁰比較の評価 -/

@[expose] public section RestrictionComparison
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 制限後に包含するH⁰関手と元のH⁰関手の比較から、指定した終域関手への自然同型を作る。 -/
def restrictHomotopyComparisonIso (F : DGFunctor A D D) (P : D → Prop)
    (hP : ∀ X, P X → P (F.obj X)) (G : HomotopyCategory A D ⥤ HomotopyCategory A D)
    (e : F.onHomotopy ≅ G) :
    (F.restrict P P hP).onHomotopy ⋙ (dgFullSubcategoryInclusion A D P).onHomotopy ≅
      (dgFullSubcategoryInclusion A D P).onHomotopy ⋙ G :=
  eqToIso ((DGFunctor.onHomotopy_comp _ _).symm.trans
    ((congrArg (fun H : DGFunctor A (DGFullSubcategory D P) D => H.onHomotopy)
      (F.restrict_comp_inclusion P P hP)).trans (DGFunctor.onHomotopy_comp _ _))) ≪≫
    Functor.isoWhiskerLeft (dgFullSubcategoryInclusion A D P).onHomotopy e

/-- 対象の性質を保つdg関手のH⁰比較は、制限して包含した対象で元の比較の成分を返す。 -/
lemma restrictHomotopyComparison_hom_app (F : DGFunctor A D D) (P : D → Prop)
    (hP : ∀ X, P X → P (F.obj X)) (G : HomotopyCategory A D ⥤ HomotopyCategory A D)
    (e : F.onHomotopy ≅ G) (X : HomotopyCategory A (DGFullSubcategory D P)) :
    (restrictHomotopyComparisonIso F P hP G e).hom.app X =
      e.hom.app ((dgFullSubcategoryInclusion A D P).onHomotopy.obj X) := by
  have h := comparisonWhiskerLeft_hom_app
    ((F.restrict P P hP).onHomotopy ⋙ (dgFullSubcategoryInclusion A D P).onHomotopy)
    (dgFullSubcategoryInclusion A D P).onHomotopy F.onHomotopy G
    ((DGFunctor.onHomotopy_comp _ _).symm.trans
      ((congrArg (fun H : DGFunctor A (DGFullSubcategory D P) D => H.onHomotopy)
        (F.restrict_comp_inclusion P P hP)).trans (DGFunctor.onHomotopy_comp _ _))) e X
  exact h.trans (Category.id_comp _)

end SerrePositivity.DifferentialGraded
end

end RestrictionComparison

/-! ## OppositeHomotopy（旧 SerrePositivity/DifferentialGraded/Category/OppositeHomotopy.lean） -/

/-! # 主ホモトピー圏からopposite dg圏の主ホモトピー圏への反変比較

## 概要
主ホモトピー圏からopposite dg圏の主ホモトピー圏への反変比較。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section OppositeHomotopy
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- Mathlibの豊穣opposite比較を主Kの商へ送る。 -/
def closedToOppositeHomotopy : ClosedCategory A D ⥤ (HomotopyCategory A Dᵒᵖ)ᵒᵖ :=
  ((forgetEnrichmentOppositeEquivalence (Complex A) D).inverse ⋙
    toHomotopy A Dᵒᵖ).rightOp

/-- 元のHom複体は同じなので、opposite比較は境界関係を保つ。 -/
lemma closedToOppositeHomotopy_boundary {x y : ClosedCategory A D} {f g : x ⟶ y}
    (h : boundaryRelation A D f g) :
    (closedToOppositeHomotopy A D).map f = (closedToOppositeHomotopy A D).map g := by
  apply Quiver.Hom.unop_inj
  apply (toHomotopy_map_eq_iff A Dᵒᵖ _ _).mpr
  exact h

/-- 主K(D)のoppositeから主K(Dᵒᵖ)への関手。smallnessは仮定しない。 -/
def homotopyOppositeFunctor : (HomotopyCategory A D)ᵒᵖ ⥤ HomotopyCategory A Dᵒᵖ :=
  (CategoryTheory.Quotient.lift (boundaryRelation A D) (closedToOppositeHomotopy A D)
    (fun _ _ _ _ h => closedToOppositeHomotopy_boundary A D h)).leftOp

end SerrePositivity.DifferentialGraded
end

end OppositeHomotopy

/-! ## TensorInclusions（旧 SerrePositivity/DifferentialGraded/Category/TensorInclusions.lean） -/

/-! # tensor積dg圏への二つの因子の包含

固定対象の閉単位を挿入し、全次数成分で単位・合成を検査する。
-/

@[expose] public section TensorInclusions
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C]

lemma dgTensor_unitElement (x : DGTensorCategory A B C) :
    (unitElement A x).val =
      dgTensorElement A (unitElement A x.1).val (unitElement A x.2).val rfl := by
  change (cycleFromUnit _ (eId (Complex A) x)).val = _
  rw [dgTensor_identity]
  exact unit_tensor_apply (eId (Complex A) x.1) (eId (Complex A) x.2)

def dgTensorFirstHom (c : C) (x y : B) :
    (x ⟶[Complex A] y) ⟶ (x ⟶[Complex A] y) ⊗ (c ⟶[Complex A] c) :=
  freeUnitInsert A c (x ⟶[Complex A] y)

lemma dgTensorFirstHom_apply (c : C) (x y : B) (p : ℤ) (f : GradedHom A x y p) :
    (dgTensorFirstHom A B C c x y).f p f =
      dgTensorElement A (x := (x, c)) (y := (y, c)) f
        (unitElement A c).val (add_zero p) :=
  freeUnitInsert_apply A c (x ⟶[Complex A] y) p f

def dgTensorSecondHom (b : B) (x y : C) :
    (x ⟶[Complex A] y) ⟶ (b ⟶[Complex A] b) ⊗ (x ⟶[Complex A] y) :=
  freeUnitInsert A b (x ⟶[Complex A] y) ≫
    (signedSwap (x ⟶[Complex A] y) (b ⟶[Complex A] b)).hom

lemma dgTensorSecondHom_apply (b : B) (x y : C) (p : ℤ) (f : GradedHom A x y p) :
    (dgTensorSecondHom A B C b x y).f p f =
      dgTensorElement A (x := (b, x)) (y := (b, y))
        (unitElement A b).val f (zero_add p) := by
  change (signedSwap (x ⟶[Complex A] y) (b ⟶[Complex A] b)).hom.f p
    ((freeUnitInsert A b (x ⟶[Complex A] y)).f p f) = _
  rw [freeUnitInsert_apply, signedSwap_apply]
  simp only [mul_zero, Int.negOnePow_zero, one_smul]
  rfl

/-- 固定した第二対象の単位を挿入するdg関手。 -/
def dgTensorIncludeFirst (c : C) : DGFunctor A B (DGTensorCategory A B C) :=
  DGFunctor.ofHomMaps A (D := B) (E := DGTensorCategory A B C)
    (fun b => ((b, c) : DGTensorCategory A B C)) (dgTensorFirstHom A B C c)
    (fun b => (dgTensorFirstHom_apply A B C c b b 0 (unitElement A b).val).trans
      (dgTensor_unitElement A B C (b, c)).symm)
    (fun x y z p q n hn f g => by
      have h := dgTensor_forward_of_sum A (x := (x, c)) (y := (y, c)) (z := (z, c))
        f (unitElement A c).val g (unitElement A c).val
        (add_zero p) (add_zero q) hn rfl hn
      have hs : dgTensorElement A (x := (x, c)) (y := (z, c)) (forward A f g hn)
          (unitElement A c).val (add_zero n) =
        forward A (D := DGTensorCategory A B C) (x := ((x, c) : DGTensorCategory A B C))
          (y := ((y, c) : DGTensorCategory A B C)) (z := ((z, c) : DGTensorCategory A B C))
          (dgTensorElement A f (unitElement A c).val (add_zero p))
          (dgTensorElement A g (unitElement A c).val (add_zero q)) hn := by
        simpa only [zero_mul, Int.negOnePow_zero, one_smul, forward_unit] using h.symm
      exact (dgTensorFirstHom_apply A B C c x z n (forward A f g hn)).trans
        (hs.trans (congrArg₂ (fun a b => forward A (D := DGTensorCategory A B C)
          (x := ((x, c) : DGTensorCategory A B C))
          (y := ((y, c) : DGTensorCategory A B C)) (z := ((z, c) : DGTensorCategory A B C)) a b hn)
          (dgTensorFirstHom_apply A B C c x y p f)
          (dgTensorFirstHom_apply A B C c y z q g)).symm))

/-- 固定した第一対象の単位を挿入するdg関手。 -/
def dgTensorIncludeSecond (b : B) : DGFunctor A C (DGTensorCategory A B C) :=
  DGFunctor.ofHomMaps A (D := C) (E := DGTensorCategory A B C)
    (fun c => ((b, c) : DGTensorCategory A B C)) (dgTensorSecondHom A B C b)
    (fun c => (dgTensorSecondHom_apply A B C b c c 0 (unitElement A c).val).trans
      (dgTensor_unitElement A B C (b, c)).symm)
    (fun x y z p q n hn f g => by
      have h := dgTensor_forward_of_sum A (x := (b, x)) (y := (b, y)) (z := (b, z))
        (unitElement A b).val f (unitElement A b).val g
        (zero_add p) (zero_add q) rfl hn hn
      have hs : dgTensorElement A (x := (b, x)) (y := (b, z)) (unitElement A b).val
          (forward A f g hn) (zero_add n) =
        forward A (D := DGTensorCategory A B C) (x := ((b, x) : DGTensorCategory A B C))
          (y := ((b, y) : DGTensorCategory A B C)) (z := ((b, z) : DGTensorCategory A B C))
          (dgTensorElement A (unitElement A b).val f (zero_add p))
          (dgTensorElement A (unitElement A b).val g (zero_add q)) hn := by
        simpa only [mul_zero, Int.negOnePow_zero, one_smul, forward_unit] using h.symm
      exact (dgTensorSecondHom_apply A B C b x z n (forward A f g hn)).trans
        (hs.trans (congrArg₂ (fun a b' => forward A (D := DGTensorCategory A B C)
          (x := ((b, x) : DGTensorCategory A B C))
          (y := ((b, y) : DGTensorCategory A B C)) (z := ((b, z) : DGTensorCategory A B C)) a b' hn)
          (dgTensorSecondHom_apply A B C b x y p f)
          (dgTensorSecondHom_apply A B C b y z q g)).symm))

end SerrePositivity.DifferentialGraded
end

end TensorInclusions

/-! ## TensorMixed（旧 SerrePositivity/DifferentialGraded/Category/TensorMixed.lean） -/

/-! # tensor積dg圏の混合作用・因子分解 -/

@[expose] public section TensorMixed
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] {B : Type v} {C : Type w}
  [DGCategory A B] [DGCategory A C]

/-- 純粋斉次Homは第一因子、第二因子の包含の豊穣順合成。 -/
lemma dgTensor_first_then_second {x y : B} {c d : C} {p q n : ℤ}
    (f : GradedHom A x y p) (g : GradedHom A c d q) (hn : p + q = n) :
    forward A (D := DGTensorCategory A B C) (x := ((x, c) : DGTensorCategory A B C))
      (y := ((y, c) : DGTensorCategory A B C)) (z := ((y, d) : DGTensorCategory A B C))
      ((dgTensorFirstHom A B C c x y).f p f)
      ((dgTensorSecondHom A B C y c d).f q g) hn =
        dgTensorElement A (x := (x, c)) (y := (y, d)) f g hn := by
  rw [dgTensorFirstHom_apply, dgTensorSecondHom_apply]
  have h := dgTensor_forward_of_sum A (x := (x, c)) (y := (y, c)) (z := (y, d))
    f (unitElement A c).val (unitElement A y).val g
    (add_zero p) (zero_add q) (add_zero p) (zero_add q) hn
  simpa only [add_zero, zero_add, zero_mul, Int.negOnePow_zero, one_smul,
    unit_forward, forward_unit] using h

/-- 逆順では二つの因子の次数積の符号を得る。 -/
lemma dgTensor_second_then_first {x y : B} {c d : C} {p q n : ℤ}
    (f : GradedHom A x y p) (g : GradedHom A c d q) (hn : q + p = n) :
    forward A (D := DGTensorCategory A B C) (x := ((x, c) : DGTensorCategory A B C))
      (y := ((x, d) : DGTensorCategory A B C)) (z := ((y, d) : DGTensorCategory A B C))
      ((dgTensorSecondHom A B C x c d).f q g)
      ((dgTensorFirstHom A B C d x y).f p f) hn =
        (q * p).negOnePow • dgTensorElement A (x := (x, c)) (y := (y, d)) f g (by omega) := by
  rw [dgTensorSecondHom_apply, dgTensorFirstHom_apply]
  have h := dgTensor_forward_of_sum A (x := (x, c)) (y := (x, d)) (z := (y, d))
    (unitElement A x).val g f (unitElement A d).val
    (zero_add q) (add_zero p) (zero_add p) (add_zero q) hn
  simpa only [add_zero, zero_add, unit_forward, forward_unit] using h

end SerrePositivity.DifferentialGraded
end

end TensorMixed

/-! ## ComplexHomotopyComparison（旧 SerrePositivity/DifferentialGraded/Category/ComplexHomotopyComparison.lean） -/

/-! # 主dg複体圏のH⁰と既存の複体ホモトピー圏の線形同値

既存complex_boundary_iffで境界関係を照合し、Mathlibのホモトピー商を比較先として使う。
-/

@[expose] public section ComplexHomotopyComparison
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CochainComplex HomComplex
variable (A : Type u) [CommRing A]

/-- 閉零複体から通常複体への既存比較はA線形である。 -/
instance closedToComplexLinear : (closedToComplex A).Linear A where
  map_smul f a := by
    apply Cochain.ofHom_injective
    rw [Cochain.ofHom_smul]
    simp only [closedToComplex, complexClosedHomEquiv_cochain]
    rfl

/-- 主dg複体圏のH⁰から、既存の非有界複体ホモトピー圏への比較。 -/
def complexHomotopyComparison : HomotopyCategory A (Complex A) ⥤
    _root_.HomotopyCategory (ModuleCat.{u} A) (.up ℤ) :=
  CategoryTheory.Quotient.lift _
    (closedToComplex A ⋙ _root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ))
    (by
      intro X Y f g h
      have hh := (complex_boundary_iff A X Y f g).mp h
      exact _root_.HomotopyCategory.eq_of_homotopy _ _ hh.some)

/-- 比較と商関手の四角形は、元の閉零比較と既存の商関手の合成に一致する。 -/
lemma complexHomotopyComparison_fac :
    toHomotopy A (Complex A) ⋙ complexHomotopyComparison A =
      closedToComplex A ⋙ _root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ) :=
  CategoryTheory.Quotient.lift_spec _ _ _

/-- 主dg複体のH⁰比較は充満。既存の商射と閉零比較の充満性を使う。 -/
instance complexHomotopyComparisonFull : (complexHomotopyComparison A).Full where
  map_surjective {X Y} f := by
    obtain ⟨X⟩ := X
    obtain ⟨Y⟩ := Y
    obtain ⟨g, rfl⟩ := (_root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)).map_surjective f
    obtain ⟨h, rfl⟩ := (closedToComplex A).map_surjective g
    exact ⟨(toHomotopy A (Complex A)).map h, rfl⟩

/-- H⁰比較は忠実。既存の商での等式からchain homotopyを取り、主境界関係へ戻す。 -/
instance complexHomotopyComparisonFaithful : (complexHomotopyComparison A).Faithful where
  map_injective {X Y} f g h := by
    obtain ⟨f, rfl⟩ := (toHomotopy A (Complex A)).map_surjective f
    obtain ⟨g, rfl⟩ := (toHomotopy A (Complex A)).map_surjective g
    have hh := _root_.HomotopyCategory.homotopyOfEq
      ((closedToComplex A).map f) ((closedToComplex A).map g) h
    exact (toHomotopy_map_eq_iff A (Complex A) f g).mpr
      ((complex_boundary_iff A _ _ f g).mpr ⟨hh⟩)

/-- 対象は実際の複体のままなので、H⁰比較は本質的全射である。 -/
instance complexHomotopyComparisonEssSurj : (complexHomotopyComparison A).EssSurj where
  mem_essImage X :=
    ⟨(toHomotopy A (Complex A)).obj (ForgetEnrichment.of (Complex A) X.as), ⟨Iso.refl _⟩⟩

/-- 主dg複体のH⁰と既存の複体ホモトピー圏の比較は同値である。 -/
instance complexHomotopyComparisonIsEquivalence : (complexHomotopyComparison A).IsEquivalence where

/-- 任意可換環上の非有界複体についてのH⁰同値。 -/
def complexHomotopyEquivalence : HomotopyCategory A (Complex A) ≌
    _root_.HomotopyCategory (ModuleCat.{u} A) (.up ℤ) :=
  (complexHomotopyComparison A).asEquivalence

/-- H⁰比較の加法性は、商の充満・本質的全射性から降下する。 -/
instance complexHomotopyComparisonAdditive : (complexHomotopyComparison A).Additive := by
  have : (toHomotopy A (Complex A) ⋙ complexHomotopyComparison A).Additive := by
    rw [complexHomotopyComparison_fac]
    infer_instance
  exact Functor.additive_of_full_essSurj_comp (toHomotopy A (Complex A)) _

/-- H⁰比較は主Hom由来のスカラー作用を既存のホモトピー商のスカラー作用へ運ぶ。 -/
instance complexHomotopyComparisonLinear : (complexHomotopyComparison A).Linear A := by
  have : (toHomotopy A (Complex A) ⋙ complexHomotopyComparison A).Linear A := by
    rw [complexHomotopyComparison_fac]
    infer_instance
  exact Functor.linear_of_full_essSurj_comp (toHomotopy A (Complex A)) _

/-- 選択した同値の順関手はA線形であり、逆関手の線形性も同値の一般APIから得られる。 -/
instance complexHomotopyEquivalenceFunctorLinear :
    (complexHomotopyEquivalence A).functor.Linear A :=
  complexHomotopyComparisonLinear A

/-- 選択した同値の順関手は加法的であり、逆関手の加法性も継承される。 -/
instance complexHomotopyEquivalenceFunctorAdditive :
    (complexHomotopyEquivalence A).functor.Additive :=
  complexHomotopyComparisonAdditive A

end SerrePositivity.DifferentialGraded
end

end ComplexHomotopyComparison
