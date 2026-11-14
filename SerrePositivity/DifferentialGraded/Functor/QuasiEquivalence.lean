module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.Logic.Small.Basic
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.EssentialImage
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Functor.QuasiEquivalence

## 概要
8 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## Basic（旧 SerrePositivity/DifferentialGraded/Functor/Basic.lean） -/

/-! # dg 関手と H⁰ 上の関手 -/

@[expose] public section Basic
universe u v w t

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A]

/-- dg 関手は Mathlib の Ch(A) 豊穣関手をそのまま用いる。 -/
@[kerodon 00PH]
abbrev DGFunctor (D : Type v) (E : Type w) [DGCategory A D] [DGCategory A E] :=
  EnrichedFunctor (Complex A) D E

variable {A} {D : Type v} {E : Type w} {T : Type t}
  [DGCategory A D] [DGCategory A E] [DGCategory A T]
namespace DGFunctor

/-- dg 恒等関手。 -/
abbrev id (D : Type v) [DGCategory A D] : DGFunctor A D D :=
  EnrichedFunctor.id (Complex A) D

/-- dg 関手の合成。Hom の chain map は同じ順に合成する。 -/
abbrev comp (F : DGFunctor A D E) (G : DGFunctor A E T) : DGFunctor A D T :=
  EnrichedFunctor.comp (Complex A) F G

/-- Z⁰ への制限。 -/
abbrev onClosed (F : DGFunctor A D E) : ClosedCategory A D ⥤ ClosedCategory A E := F.forget

/-- dg 関手の Z⁰ への制限は加法的。 -/
instance onClosedAdditive (F : DGFunctor A D E) : F.onClosed.Additive where
  map_add := by
    intro x y f g
    change (ForgetEnrichment.homTo (Complex A) f + ForgetEnrichment.homTo (Complex A) g) ≫
      F.map (ForgetEnrichment.to (Complex A) x) (ForgetEnrichment.to (Complex A) y) =
      ForgetEnrichment.homTo (Complex A) f ≫
        F.map (ForgetEnrichment.to (Complex A) x) (ForgetEnrichment.to (Complex A) y) +
      ForgetEnrichment.homTo (Complex A) g ≫
        F.map (ForgetEnrichment.to (Complex A) x) (ForgetEnrichment.to (Complex A) y)
    apply Preadditive.add_comp

/-- dg 関手の Z⁰ への制限は A 線形。 -/
instance onClosedLinear (F : DGFunctor A D E) : F.onClosed.Linear A where
  map_smul := by
    intro x y f a
    change (a • ForgetEnrichment.homTo (Complex A) f) ≫
      F.map (ForgetEnrichment.to (Complex A) x) (ForgetEnrichment.to (Complex A) y) =
      a • (ForgetEnrichment.homTo (Complex A) f ≫
        F.map (ForgetEnrichment.to (Complex A) x) (ForgetEnrichment.to (Complex A) y))
    apply CategoryTheory.Linear.smul_comp

/-- dg 関手は境界関係を保存する。Hom chain map とホモトピーの後合成を用いる。 -/
lemma preserves_boundary (F : DGFunctor A D E) {x y : ClosedCategory A D}
    (f g : x ⟶ y) (h : boundaryRelation A D f g) :
    boundaryRelation A E (F.onClosed.map f) (F.onClosed.map g) :=
  ⟨h.some.compRight (F.map x y)⟩

/-- 境界商の普遍性による H⁰ 関手。 -/
def onHomotopy (F : DGFunctor A D E) : HomotopyCategory A D ⥤ HomotopyCategory A E :=
  CategoryTheory.Quotient.lift _ (F.onClosed ⋙ toHomotopy A E) (by
    intro x y f g h
    apply (toHomotopy_map_eq_iff A E _ _).2
    exact F.preserves_boundary f g h)

/-- 商への関手の四角形は可換。 -/
lemma onHomotopy_fac (F : DGFunctor A D E) :
    toHomotopy A D ⋙ F.onHomotopy = F.onClosed ⋙ toHomotopy A E :=
  CategoryTheory.Quotient.lift_spec _ _ _

/-- H⁰ 関手は加法的。 -/
instance onHomotopyAdditive (F : DGFunctor A D E) : F.onHomotopy.Additive := by
  have : (toHomotopy A D ⋙ F.onHomotopy).Additive := by
    rw [onHomotopy_fac]
    infer_instance
  exact CategoryTheory.Functor.additive_of_full_essSurj_comp (toHomotopy A D) F.onHomotopy

/-- H⁰ 関手は A 線形。 -/
instance onHomotopyLinear (F : DGFunctor A D E) : F.onHomotopy.Linear A := by
  have : (toHomotopy A D ⋙ F.onHomotopy).Linear A := by
    rw [onHomotopy_fac]
    infer_instance
  exact CategoryTheory.Functor.linear_of_full_essSurj_comp (toHomotopy A D) F.onHomotopy

/-- H⁰ 関手は恒等関手を保存する。 -/
lemma onHomotopy_id : (id (A := A) D).onHomotopy = 𝟭 (HomotopyCategory A D) := by
  apply Quotient.lift_unique'
  apply CategoryTheory.Functor.ext
  · intro x y f
    simp [onHomotopy, EnrichedFunctor.forget, EnrichedFunctor.id,
      CategoryTheory.Quotient.lift, CategoryTheory.Quotient.functor, id]
  · intro x
    rfl

/-- H⁰ 関手は合成を保存する。 -/
lemma onHomotopy_comp (F : DGFunctor A D E) (G : DGFunctor A E T) :
    (comp F G).onHomotopy = F.onHomotopy ⋙ G.onHomotopy := by
  apply Quotient.lift_unique'
  apply CategoryTheory.Functor.ext
  · intro x y f
    simp [onHomotopy, EnrichedFunctor.forget, EnrichedFunctor.comp,
      CategoryTheory.Quotient.lift, CategoryTheory.Quotient.functor, comp]
    rfl
  · intro x
    rfl
end DGFunctor
end SerrePositivity.DifferentialGraded
end

end Basic

/-! ## Small（旧 SerrePositivity/DifferentialGraded/Functor/Small.lean） -/

/-!
概要：二つの小さい dg 対象型の間の厳密 dg 関手型も同じ宇宙で小さいことを示す。
方針：対象写像と全 Hom 鎖写像の依存対へ埋め込み、圏法則の証明を無視する。
規約：元の対象宇宙は独立でよい。全加群圏を小さいとは仮定しない。
使われ方：小さい出発提示を大きい対象宇宙の小 dg 圏へ送るラベル型の評価。
-/

@[expose] public section Small
universe u v w

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (R : Type u) [CommRing R] (C : Type v) (D : Type w)
  [DGCategory R C] [DGCategory R D] [Small.{u} C] [Small.{u} D]

lemma dgFunctor_small : Small.{u} (DGFunctor R C D) := by
  let data := fun F : DGFunctor R C D =>
    (⟨F.obj, F.map⟩ : Σ f : C → D, ∀ x y, homObject R C x y ⟶ homObject R D (f x) (f y))
  apply small_of_injective (f := data)
  rintro ⟨fo, fm, fi, fc⟩ ⟨go, gm, gi, gc⟩ h
  have ho : fo = go := congrArg Sigma.fst h
  subst go
  have hm : fm = gm := eq_of_heq ((Sigma.mk.inj_iff.mp h).2)
  subst gm
  rfl

attribute [instance] dgFunctor_small

end SerrePositivity.DifferentialGraded
end

end Small

/-! ## HomIso（旧 SerrePositivity/DifferentialGraded/Functor/HomIso.lean） -/

/-! # 全Homの同型から閉零圏・H⁰の完全忠実性へ

全Hom写像がchain isoであるdg関手について、逆chain mapで境界を反映する。
-/

@[expose] public section HomIso
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGFunctor
open CategoryTheory MonoidalCategory HomologicalComplex
variable {A : Type u} [CommRing A] {D : Type v} {E : Type w}
  [DGCategory A D] [DGCategory A E] (F : DGFunctor A D E)
  (hF : ∀ x y, IsIso (F.map x y))

include hF

/-- 全Hom写像が同型なら閉零関手は充満。 -/
lemma onClosed_full_of_homIso : F.onClosed.Full where
  map_surjective {x y} f := by
    let := hF x y
    let f' : 𝟙_ (Complex A) ⟶ homObject A E (F.obj x) (F.obj y) :=
      ForgetEnrichment.homTo (Complex A) f
    change ∃ g : 𝟙_ (Complex A) ⟶ homObject A D x y, g ≫ F.map x y = f'
    refine ⟨f' ≫ inv (F.map x y), ?_⟩
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- 全Hom写像が同型なら閉零関手は忠実。 -/
lemma onClosed_faithful_of_homIso : F.onClosed.Faithful where
  map_injective {x y} f g h := by
    let := hF x y
    exact (cancel_mono (F.map x y)).mp h

/-- Homの逆chain mapにより、dg関手は境界関係を反映する。 -/
lemma boundary_iff_of_homIso {x y : ClosedCategory A D} (f g : x ⟶ y) :
    boundaryRelation A E (F.onClosed.map f) (F.onClosed.map g) ↔
      boundaryRelation A D f g := by
  constructor
  · rintro ⟨h⟩
    let := hF x y
    have h' : Homotopy
        ((ForgetEnrichment.homTo (Complex A) f ≫ F.map x y) ≫ inv (F.map x y))
        ((ForgetEnrichment.homTo (Complex A) g ≫ F.map x y) ≫ inv (F.map x y)) :=
      h.compRight (inv (F.map x y))
    change Nonempty (Homotopy (ForgetEnrichment.homTo (Complex A) f)
      (ForgetEnrichment.homTo (Complex A) g))
    simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] using Nonempty.intro h'
  · exact F.preserves_boundary f g

/-- 全Homが同型ならH⁰関手は充満。 -/
lemma onHomotopy_full_of_homIso : F.onHomotopy.Full where
  map_surjective {x y} f := by
    let := F.onClosed_full_of_homIso hF
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    obtain ⟨f, rfl⟩ := (toHomotopy A E).map_surjective f
    obtain ⟨g, rfl⟩ := F.onClosed.map_surjective f
    exact ⟨(toHomotopy A D).map g, rfl⟩

/-- 全Homが同型ならH⁰関手は忠実。 -/
lemma onHomotopy_faithful_of_homIso : F.onHomotopy.Faithful where
  map_injective {x y} f g h := by
    obtain ⟨f, rfl⟩ := (toHomotopy A D).map_surjective f
    obtain ⟨g, rfl⟩ := (toHomotopy A D).map_surjective g
    exact (toHomotopy_map_eq_iff A D f g).mpr
      ((F.boundary_iff_of_homIso hF f g).mp ((toHomotopy_map_eq_iff A E _ _).mp h))

end SerrePositivity.DifferentialGraded.DGFunctor
end

end HomIso

/-! ## Components（旧 SerrePositivity/DifferentialGraded/Functor/Components.lean） -/

/-! # 斉次成分の単位・合成式からのdg関手構成 -/

@[expose] public section Components
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGFunctor
open CategoryTheory MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] {D : Type v} {E : Type w}
  [DGCategory A D] [DGCategory A E]

/-- Homのchain mapに対して斉次単位・合成式を与える構成子。 -/
def ofHomMaps (F : D → E) (H : ∀ (x y : D), (x ⟶[Complex A] y) ⟶ (F x ⟶[Complex A] F y))
    (hi : ∀ x, (H x x).f 0 (unitElement A x).val = (unitElement A (F x)).val)
    (hc : ∀ (x y z : D) (p q n : ℤ) (hn : p + q = n)
      (f : GradedHom A x y p) (g : GradedHom A y z q),
      (H x z).f n (forward A f g hn) =
        forward A ((H x y).f p f) ((H y z).f q g) hn) : DGFunctor A D E where
  obj := F
  map := H
  map_id x := by
    apply (unitCycleEquiv _).injective
    apply Subtype.ext
    change (cycleFromUnit _ (eId (Complex A) x ≫ H x x)).val =
      (cycleFromUnit _ (eId (Complex A) (F x))).val
    rw [cycleFromUnit_postcomp]
    exact hi x
  map_comp x y z := by
    apply tensorHom_ext
    intro p q n hn
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro f g
    change (H x z).f n (forward A f g hn) =
      (eComp (Complex A) (F x) (F y) (F z)).f n
        ((H x y ⊗ₘ H y z).f n
          (ιTensorObj (x ⟶[Complex A] y) (y ⟶[Complex A] z) p q n hn (f ⊗ₜ[A] g)))
    rw [tensorMap_apply]
    exact hc x y z p q n hn f g

/-- dg関手は単位の零次数cycleを保存する。 -/
lemma map_unitElement (F : DGFunctor A D E) (x : D) :
    (F.map x x).f 0 (unitElement A x).val = (unitElement A (F.obj x)).val := by
  have h := congrArg (fun f => (cycleFromUnit _ f).val) (F.map_id x)
  rw [cycleFromUnit_postcomp] at h
  exact h

/-- dg関手は任意次数の豊穣順合成を保存する。 -/
lemma map_forward (F : DGFunctor A D E) {x y z : D} {p q n : ℤ}
    (f : GradedHom A x y p) (g : GradedHom A y z q) (hn : p + q = n) :
    (F.map x z).f n (forward A f g hn) =
      forward A ((F.map x y).f p f) ((F.map y z).f q g) hn := by
  have h := congrArg (fun l => l.f n
    (ιTensorObj (x ⟶[Complex A] y) (y ⟶[Complex A] z) p q n hn (f ⊗ₜ[A] g)))
    (F.map_comp x y z)
  change (F.map x z).f n (forward A f g hn) =
    (eComp (Complex A) (F.obj x) (F.obj y) (F.obj z)).f n
      ((F.map x y ⊗ₘ F.map y z).f n
        (ιTensorObj (x ⟶[Complex A] y) (y ⟶[Complex A] z) p q n hn (f ⊗ₜ[A] g))) at h
  rw [tensorMap_apply] at h
  exact h

end SerrePositivity.DifferentialGraded.DGFunctor
end

end Components

/-! ## FullHomLift（旧 SerrePositivity/DifferentialGraded/Functor/FullHomLift.lean） -/

/-!
概要：全 Hom 鎖写像が同型である dg 関手に沿って、指定された関手成分を持ち上げる。
方針：同じ対象ラベルで Hom の逆鎖写像を合成し、単位・合成を同型の単射性で反映する。
規約：対象の全射性を仮定せず、指定対象写像と元の全 Hom 成分を入力に保持する。
使われ方：c′ の実係数閉包から固定基底コードへ元の出発 dg 関手を輸送する。
-/

@[expose] public section FullHomLift
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
  (E : Type w) [DGCategory R E] (F : DGFunctor R D E)
  (hF : ∀ x y, IsIso (F.map x y))
  (C : Type z) [DGCategory R C] (obj : C → D)
  (map : ∀ x y, homObject R C x y ⟶ homObject R E (F.obj (obj x)) (F.obj (obj y)))
  (hu : ∀ x, eId (Complex R) x ≫ map x x = eId (Complex R) (F.obj (obj x)))
  (hc : ∀ x y z, eComp (Complex R) x y z ≫ map x z =
    (map x y ⊗ₘ map y z) ≫ eComp (Complex R) (F.obj (obj x)) (F.obj (obj y)) (F.obj (obj z)))

def dgFunctorFullHomLift : DGFunctor R C D := by
  letI (x y : D) : IsIso (F.map x y) := hF x y
  exact
    { obj := obj
      map x y := map x y ≫ inv (F.map (obj x) (obj y))
      map_id x := by
        apply (cancel_mono (F.map (obj x) (obj x))).1
        simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
        exact (hu x).trans (F.map_id (obj x)).symm
      map_comp x y z := by
        apply (cancel_mono (F.map (obj x) (obj z))).1
        simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
        rw [F.map_comp (obj x) (obj y) (obj z)]
        rw [tensorHom_comp_tensorHom_assoc]
        simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
        exact hc x y z }

lemma dgFunctorFullHomLift_map (x y : C) :
    (dgFunctorFullHomLift R D E F hF C obj map hu hc).map x y ≫
      F.map (obj x) (obj y) = map x y := by
  letI (x y : D) : IsIso (F.map x y) := hF x y
  change (map x y ≫ inv (F.map (obj x) (obj y))) ≫ F.map (obj x) (obj y) = _
  simp

end SerrePositivity.DifferentialGraded
end

end FullHomLift

/-! ## ComplexValued（旧 SerrePositivity/DifferentialGraded/Functor/ComplexValued.lean） -/

/-! # 複体に値を持つdg関手のcochain合成計算 -/

@[expose] public section ComplexValued
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGFunctor
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

lemma map_forward_cochain (F : DGFunctor A D (Complex A)) {x y z : D} {p q n : ℤ}
    (f : GradedHom A x y p) (g : GradedHom A y z q) (hn : p + q = n) :
    (F.map x z).f n (forward A f g hn) =
      (p * q).negOnePow • ((F.map x y).f p f).comp ((F.map y z).f q g) hn := by
  have h := map_forward A F f g hn
  change (F.map x z).f n (forward A f g hn) =
    (enrichedComposition _ _ _).f n
      (ιTensorObj (homComplex A (F.obj x) (F.obj y)) (homComplex A (F.obj y) (F.obj z))
        p q n hn ((F.map x y).f p f ⊗ₜ[A] (F.map y z).f q g)) at h
  exact h.trans (enrichedComposition_apply _ _ _ p q n hn _ _)

end SerrePositivity.DifferentialGraded.DGFunctor
end

end ComplexValued

/-! ## QuasiEquivalence（旧 SerrePositivity/DifferentialGraded/Functor/QuasiEquivalence.lean） -/

/-! # 準同値

各 Hom の準同型と H⁰ の本質的全射を独立に要求する。
Morita 同値・通常の圏同値と同一視しない。
-/

@[expose] public section QuasiEquivalence
universe u v w t

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable {A : Type u} [CommRing A] {D : Type v} {E : Type w} {T : Type t}
  [DGCategory A D] [DGCategory A E] [DGCategory A T]

/-- dg 関手が各 Hom 複体で準同型を誘導するという条件。 -/
def HomQuasiIso (F : DGFunctor A D E) : Prop := ∀ x y, QuasiIso (F.map x y)

/-- 準同値は Hom 準同型と H⁰ の本質的全射の二条件。 -/
def QuasiEquivalence (F : DGFunctor A D E) : Prop :=
  HomQuasiIso F ∧ F.onHomotopy.EssSurj

/-- dg 恒等関手は各 Hom で準同型。 -/
lemma homQuasiIso_id : HomQuasiIso (DGFunctor.id (A := A) D) := by
  intro x y
  change QuasiIso (𝟙 _)
  constructor
  intro i
  exact quasiIsoAt_of_isIso (𝟙 (x ⟶[Complex A] y)) i

/-- Hom 準同型条件は合成に安定。 -/
lemma homQuasiIso_comp (F : DGFunctor A D E) (G : DGFunctor A E T)
    (hF : HomQuasiIso F) (hG : HomQuasiIso G) : HomQuasiIso (DGFunctor.comp F G) := by
  intro x y
  have := hF x y
  have := hG (F.obj x) (F.obj y)
  change QuasiIso (F.map x y ≫ G.map (F.obj x) (F.obj y))
  infer_instance

/-- dg 恒等関手は準同値。 -/
lemma quasiEquivalence_id : QuasiEquivalence (DGFunctor.id (A := A) D) := by
  refine ⟨homQuasiIso_id, ?_⟩
  rw [DGFunctor.onHomotopy_id]
  infer_instance

/-- 準同値は合成に安定。二条件をそれぞれ証明する。 -/
lemma quasiEquivalence_comp (F : DGFunctor A D E) (G : DGFunctor A E T)
    (hF : QuasiEquivalence F) (hG : QuasiEquivalence G) :
    QuasiEquivalence (DGFunctor.comp F G) := by
  refine ⟨homQuasiIso_comp F G hF.1 hG.1, ?_⟩
  have := hF.2
  have := hG.2
  rw [DGFunctor.onHomotopy_comp]
  infer_instance
end SerrePositivity.DifferentialGraded
end

end QuasiEquivalence

/-! ## QuasiIsoHomology（旧 SerrePositivity/DifferentialGraded/Functor/QuasiIsoHomology.lean） -/

/-! # Hom準同型からH⁰関手の完全忠実性へ

## 概要
Hom準同型からH⁰関手の完全忠実性へ。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section QuasiIsoHomology
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGFunctor
open CategoryTheory HomologicalComplex
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]
  {E : Type w} [DGCategory A E] (F : DGFunctor A D E)

lemma closedHomEquiv_map {x y : ClosedCategory A D} (f : x ⟶ y) :
    closedHomEquiv A E (F.onClosed.obj x) (F.onClosed.obj y) (F.onClosed.map f) =
      complexMapZeroCycle A (F.map x y) (closedHomEquiv A D x y f) := by
  apply Subtype.ext
  change (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f ≫ F.map x y)).val = _
  rw [cycleFromUnit_postcomp]
  rfl

lemma homotopyHomologyEquiv_map_naturality {x y : ClosedCategory A D}
    (f : (toHomotopy A D).obj x ⟶ (toHomotopy A D).obj y) :
    homotopyHomologyEquiv A E (F.onClosed.obj x) (F.onClosed.obj y) (F.onHomotopy.map f) =
      homologyMap (F.map x y) 0 (homotopyHomologyEquiv A D x y f) := by
  obtain ⟨g, rfl⟩ := (toHomotopy A D).map_surjective f
  change homotopyHomologyEquiv A E (F.onClosed.obj x) (F.onClosed.obj y)
    ((toHomotopy A E).map (F.onClosed.map g)) = _
  rw [homotopyHomologyEquiv_map, homotopyHomologyEquiv_map,
    complexZeroHomologyClass_naturality, closedHomEquiv_map]
  rfl

lemma onHomotopy_map_bijective_of_homQuasiIso (hF : HomQuasiIso F)
    (x y : ClosedCategory A D) :
    Function.Bijective (fun f : (toHomotopy A D).obj x ⟶ (toHomotopy A D).obj y =>
      F.onHomotopy.map f) := by
  let : QuasiIso (F.map x y) := hF x y
  let e := homotopyHomologyEquiv A D x y
  let e' := homotopyHomologyEquiv A E (F.onClosed.obj x) (F.onClosed.obj y)
  let b := (asIso (homologyMap (F.map x y) 0)).toLinearEquiv.toEquiv
  let k := (e.trans b).trans e'.symm
  have hk : (fun f : (toHomotopy A D).obj x ⟶ (toHomotopy A D).obj y =>
      F.onHomotopy.map f) = k := by
    funext f
    apply e'.injective
    change homotopyHomologyEquiv A E (F.onClosed.obj x) (F.onClosed.obj y)
      (F.onHomotopy.map f) = e' (e'.symm (b (e f)))
    rw [e'.apply_symm_apply]
    exact F.homotopyHomologyEquiv_map_naturality f
  rw [hk]
  exact k.bijective

lemma onHomotopy_full_of_homQuasiIso (hF : HomQuasiIso F) : F.onHomotopy.Full where
  map_surjective {x y} := by
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    exact (F.onHomotopy_map_bijective_of_homQuasiIso hF x y).2

lemma onHomotopy_faithful_of_homQuasiIso (hF : HomQuasiIso F) : F.onHomotopy.Faithful where
  map_injective {x y} := by
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    exact (F.onHomotopy_map_bijective_of_homQuasiIso hF x y).1

end SerrePositivity.DifferentialGraded.DGFunctor
end

end QuasiIsoHomology

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.3.1.18"] _root_.SerrePositivity.DifferentialGraded.DGFunctor
