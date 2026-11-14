module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying
public import SerrePositivity.DifferentialGraded.Category.Basic
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
public import Mathlib.CategoryTheory.Enriched.Opposite
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Triangulated.Functor
public import SerrePositivity.DifferentialGraded.Complexes.HomLimits
public import SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochain
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation

/-!
# Module.Basic

## 概要
13 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## Basic（旧 SerrePositivity/DifferentialGraded/Module/Basic.lean） -/

/-! # 右 dg 加群

対象は Dᵒᵖ から Ch(A) への豊穣関手であり、通常の関手圏に置き換えない。
-/

@[expose] public section Basic
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 右 dg 加群の対象は既存の豊穣関手。
型別名は全次数自然性を持つ射の圏構造を選ぶためのもので、対象データを複製しない。 -/
def RightModule := DGFunctor A Dᵒᵖ (Complex A)

/-- 左 dg 加群の対象。 -/
abbrev LeftModule := DGFunctor A D (Complex A)

namespace RightModule
variable {A D}

/-- 右加群の対象データを既存の豊穣関手として読む。 -/
abbrev toFunctor (M : RightModule A D) : DGFunctor A Dᵒᵖ (Complex A) := M

/-- 豊穣関手を右加群の対象として読む。 -/
abbrev ofFunctor (F : DGFunctor A Dᵒᵖ (Complex A)) : RightModule A D := F

/-- 右加群の対象での値。 -/
abbrev obj (M : RightModule A D) (x : Dᵒᵖ) : Complex A := M.toFunctor.obj x

/-- 右加群の全次数 Hom 射。 -/
abbrev map (M : RightModule A D) (x y : Dᵒᵖ) :
    (x ⟶[Complex A] y) ⟶ homComplex A (M.obj x) (M.obj y) := M.toFunctor.map x y
end RightModule

/-- 対象データの型別名の往復は定義上の恒等写像。 -/
lemma rightModule_roundtrip (M : RightModule A D) :
    RightModule.ofFunctor M.toFunctor = M := rfl

/-- 右加群の対象 x での値。射の評価関手は全次数自然性の圏構造の後に構成する。 -/
abbrev moduleValue (x : D) (M : RightModule A D) : Complex A := M.obj (op x)

/-- 豊穣 opposite の Hom は順を逆にした元の Hom 複体。 -/
lemma opposite_hom (x y : Dᵒᵖ) :
    EnrichedCategory.Hom (V := Complex A) x y =
      EnrichedCategory.Hom (V := Complex A) y.unop x.unop := rfl

/-- 豊穣 opposite の合成には Koszul braiding が入る。 -/
lemma opposite_composition (x y z : Dᵒᵖ) :
    eComp (Complex A) x y z =
      (signedSwap (y.unop ⟶[Complex A] x.unop) (z.unop ⟶[Complex A] y.unop)).hom ≫
        eComp (Complex A) z.unop y.unop x.unop := rfl

/-- 豊穣順の opposite 合成の斉次公式。 -/
lemma opposite_forward (x y z : Dᵒᵖ) (p q n : ℤ) (hn : p + q = n)
    (f : GradedHom A x y p) (g : GradedHom A y z q) :
    forward A f g hn = (p * q).negOnePow •
      forward A (x := z.unop) (y := y.unop) (z := x.unop) g f (by omega) := by
  unfold forward
  rw [opposite_composition A D x y z]
  change (eComp (Complex A) z.unop y.unop x.unop).f n
    ((signedSwap (y.unop ⟶[Complex A] x.unop) (z.unop ⟶[Complex A] y.unop)).hom.f n
      (ιTensorObj (y.unop ⟶[Complex A] x.unop) (z.unop ⟶[Complex A] y.unop)
        p q n hn (f ⊗ₜ[A] g))) = _
  rw [signedSwap_apply]
  simp only [Units.smul_def, map_zsmul]

/-- 通常順の opposite 合成は元の逆順合成に (-1)^(pq) を掛ける。 -/
lemma opposite_compose (x y z : Dᵒᵖ) (p q n : ℤ) (hn : p + q = n)
    (f : GradedHom A x y p) (g : GradedHom A y z q) :
    compose A g f hn = (p * q).negOnePow •
      compose A (x := z.unop) (y := y.unop) (z := x.unop) f g (by omega) := by
  unfold compose forward
  rw [opposite_composition]
  change (p * q).negOnePow •
    (eComp (Complex A) z.unop y.unop x.unop).f n
      ((signedSwap (y.unop ⟶[Complex A] x.unop)
        (z.unop ⟶[Complex A] y.unop)).hom.f n
          (ιTensorObj (y.unop ⟶[Complex A] x.unop) (z.unop ⟶[Complex A] y.unop)
            p q n hn (f ⊗ₜ[A] g))) = _
  rw [signedSwap_apply]
  simp only [Units.smul_def, map_zsmul, smul_smul, mul_comm p q]
end SerrePositivity.DifferentialGraded
end

end Basic

/-! ## Hom（旧 SerrePositivity/DifferentialGraded/Module/Hom.lean） -/

/-! # 右 dg 加群の Hom end

全豊穣 Hom に対する自然性を二つの chain map の equalizer として課す。
閉次数零の射だけに対する通常の自然性では代用しない。
対象族 D が Hom 加群の宇宙 u に small であることを明示する。
-/

@[expose] public section Hom
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

local instance : HasProductsOfShape D (ModuleCat.{u} A) := ModuleCat.hasLimitsOfShape
local instance : HasProductsOfShape (D × D) (ModuleCat.{u} A) := ModuleCat.hasLimitsOfShape

/-- 全対象上の Hom 複体の直積。 -/
abbrev homFamily (M N : RightModule A D) : D → Complex A :=
  fun x => homComplex A (M.obj (op x)) (N.obj (op x))

/-- 自然変換候補の全対象での直積。 -/
abbrev homCandidates (M N : RightModule A D) : Complex A := ∏ᶜ homFamily A D M N

/-- 全豊穣 Hom に関する自然性の値域。二重 Hom で全次数を保持する。 -/
abbrev homRelations (M N : RightModule A D) : D × D → Complex A :=
  fun xy => homComplex A (op xy.1 ⟶[Complex A] op xy.2)
    (homComplex A (M.obj (op xy.1)) (N.obj (op xy.2)))

/-- 自然性の左辺の転置前の chain map。 -/
def homNaturalityLeft (M N : RightModule A D) (x y : D) :
    homCandidates A D M N ⊗ (op x ⟶[Complex A] op y) ⟶
      homComplex A (M.obj (op x)) (N.obj (op y)) :=
  (β_ _ _).hom ≫ (M.map (op x) (op y) ⊗ₘ Pi.π (homFamily A D M N) y) ≫
    enrichedComposition (M.obj (op x)) (M.obj (op y)) (N.obj (op y))

/-- 自然性の右辺の転置前の chain map。 -/
def homNaturalityRight (M N : RightModule A D) (x y : D) :
    homCandidates A D M N ⊗ (op x ⟶[Complex A] op y) ⟶
      homComplex A (M.obj (op x)) (N.obj (op y)) :=
  (Pi.π (homFamily A D M N) x ⊗ₘ N.map (op x) (op y)) ≫
    enrichedComposition (M.obj (op x)) (N.obj (op x)) (N.obj (op y))

/-- 全対の自然性の左辺を同時に保持する射。 -/
def homRelationsLeft (M N : RightModule A D) :
    homCandidates A D M N ⟶ ∏ᶜ homRelations A D M N :=
  Pi.lift (fun xy => curryRight (homNaturalityLeft A D M N xy.1 xy.2))

/-- 全対の自然性の右辺を同時に保持する射。 -/
def homRelationsRight (M N : RightModule A D) :
    homCandidates A D M N ⟶ ∏ᶜ homRelations A D M N :=
  Pi.lift (fun xy => curryRight (homNaturalityRight A D M N xy.1 xy.2))

/-- 右 dg 加群の Hom 複体。全次数の豊穣自然性を課す end。 -/
abbrev moduleHom (M N : RightModule A D) : Complex A :=
  equalizer (homRelationsLeft A D M N) (homRelationsRight A D M N)

/-- Hom end の対象 x における評価 chain map。 -/
abbrev moduleHomπ (M N : RightModule A D) (x : D) :
    moduleHom A D M N ⟶ homComplex A (M.obj (op x)) (N.obj (op x)) :=
  equalizer.ι _ _ ≫ Pi.π (homFamily A D M N) x

/-- Hom end への射は全対象の成分で判定できる。 -/
lemma moduleHom_ext {M N : RightModule A D} {K : Complex A}
    {f g : K ⟶ moduleHom A D M N}
    (h : ∀ x, f ≫ moduleHomπ A D M N x = g ≫ moduleHomπ A D M N x) : f = g := by
  apply equalizer.hom_ext
  apply Pi.hom_ext
  intro x
  exact h x
/-- Hom 候補への射を自然性の左辺へ前合成する公式。 -/
lemma homNaturalityLeft_precomp (M N : RightModule A D) {K : Complex A}
    (k : K ⟶ homCandidates A D M N) (x y : D) :
    (k ⊗ₘ 𝟙 (op x ⟶[Complex A] op y)) ≫ homNaturalityLeft A D M N x y =
      (β_ K (op x ⟶[Complex A] op y)).hom ≫
        (M.map (op x) (op y) ⊗ₘ (k ≫ Pi.π (homFamily A D M N) y)) ≫
          enrichedComposition (M.obj (op x)) (M.obj (op y)) (N.obj (op y)) := by
  dsimp only [homNaturalityLeft]
  rw [← Category.assoc, ← Category.assoc, BraidedCategory.braiding_naturality,
    Category.assoc, Category.assoc, tensorHom_comp_tensorHom_assoc]
  simp

/-- Hom 候補への射を自然性の右辺へ前合成する公式。 -/
lemma homNaturalityRight_precomp (M N : RightModule A D) {K : Complex A}
    (k : K ⟶ homCandidates A D M N) (x y : D) :
    (k ⊗ₘ 𝟙 (op x ⟶[Complex A] op y)) ≫ homNaturalityRight A D M N x y =
      ((k ≫ Pi.π (homFamily A D M N) x) ⊗ₘ N.map (op x) (op y)) ≫
        enrichedComposition (M.obj (op x)) (N.obj (op x)) (N.obj (op y)) := by
  dsimp only [homNaturalityRight]
  rw [tensorHom_comp_tensorHom_assoc]
  simp

/-- Hom end に入るための条件は全次数の豊穣自然性と同値。 -/
lemma homRelations_eq_iff (M N : RightModule A D) {K : Complex A}
    (k : K ⟶ homCandidates A D M N) :
    k ≫ homRelationsLeft A D M N = k ≫ homRelationsRight A D M N ↔
      ∀ x y : D,
        (β_ K (op x ⟶[Complex A] op y)).hom ≫
          (M.map (op x) (op y) ⊗ₘ (k ≫ Pi.π (homFamily A D M N) y)) ≫
            enrichedComposition (M.obj (op x)) (M.obj (op y)) (N.obj (op y)) =
        ((k ≫ Pi.π (homFamily A D M N) x) ⊗ₘ N.map (op x) (op y)) ≫
          enrichedComposition (M.obj (op x)) (N.obj (op x)) (N.obj (op y)) := by
  constructor
  · intro h x y
    have hp := congrArg (fun f => f ≫ Pi.π (homRelations A D M N) (x, y)) h
    simp only [homRelationsLeft, homRelationsRight, Category.assoc, homRelations,
      Pi.lift_comp_π] at hp
    have ht := congrArg uncurryRight hp
    rw [← curryRight_naturality_source, ← curryRight_naturality_source,
      uncurryRight_curryRight, uncurryRight_curryRight,
      homNaturalityLeft_precomp, homNaturalityRight_precomp] at ht
    exact ht
  · intro h
    apply Pi.hom_ext
    rintro ⟨x, y⟩
    simp only [homRelationsLeft, homRelationsRight, Category.assoc, homRelations,
      Pi.lift_comp_π]
    rw [← curryRight_naturality_source, ← curryRight_naturality_source,
      homNaturalityLeft_precomp, homNaturalityRight_precomp, h x y]

/-- パラメータ K を持つ全次数の豊穣自然変換。Mathlib の GradedNatTrans を再利用する。 -/
abbrev ModuleParamTrans (K : Complex A) (M N : RightModule A D) :=
  GradedNatTrans ((Center.ofBraided (Complex A)).obj K) M.toFunctor N.toFunctor

/-- Hom end の普遍性：射 K→Hom(M,N) は K パラメータ付き豊穣自然変換。 -/
def moduleHomEquiv (K : Complex A) (M N : RightModule A D) :
    (K ⟶ moduleHom A D M N) ≃ ModuleParamTrans A D K M N where
  toFun f :=
    { app x := f ≫ moduleHomπ A D M N x.unop
      naturality x y := by
        have hh := congrArg (fun l => f ≫ l) (equalizer.condition
          (homRelationsLeft A D M N) (homRelationsRight A D M N))
        rw [← Category.assoc, ← Category.assoc] at hh
        have hp := (homRelations_eq_iff A D M N _).1 hh x.unop y.unop
        exact hp }
  invFun τ := equalizer.lift (Pi.lift (fun x => τ.app (op x))) (by
    apply (homRelations_eq_iff A D M N _).2
    intro x y
    simp only [homFamily, Pi.lift_comp_π]
    exact τ.naturality (op x) (op y))
  left_inv f := by
    apply moduleHom_ext
    intro x
    simp only [moduleHomπ, equalizer.lift_ι_assoc, Pi.lift_comp_π]
  right_inv τ := by
    apply GradedNatTrans.ext
    funext x
    simp only [moduleHomπ, equalizer.lift_ι_assoc, Pi.lift_comp_π]
/-- Hom end に持ち上げた自然変換の評価は元の成分。 -/
@[reassoc (attr := simp)]
lemma moduleHomEquiv_symm_π (K : Complex A) (M N : RightModule A D)
    (τ : ModuleParamTrans A D K M N) (x : D) :
    (moduleHomEquiv A D K M N).symm τ ≫ moduleHomπ A D M N x = τ.app (op x) := by
  simp only [moduleHomEquiv, Equiv.coe_fn_symm_mk, moduleHomπ,
    equalizer.lift_ι_assoc, Pi.lift_comp_π]
/-- Hom end の評価族は全豊穣 Hom に関して自然。 -/
lemma moduleHomπ_naturality (M N : RightModule A D) (x y : Dᵒᵖ) :
    (β_ (moduleHom A D M N) (x ⟶[Complex A] y)).hom ≫
      (M.map x y ⊗ₘ moduleHomπ A D M N y.unop) ≫ enrichedComposition _ _ _ =
    (moduleHomπ A D M N x.unop ⊗ₘ N.map x y) ≫ enrichedComposition _ _ _ := by
  have h := (moduleHomEquiv A D (moduleHom A D M N) M N (𝟙 _)).naturality x y
  change (β_ (moduleHom A D M N) (x ⟶[Complex A] y)).hom ≫
      (M.map x y ⊗ₘ (𝟙 _ ≫ moduleHomπ A D M N y.unop)) ≫ enrichedComposition _ _ _ =
    ((𝟙 _ ≫ moduleHomπ A D M N x.unop) ⊗ₘ N.map x y) ≫ enrichedComposition _ _ _ at h
  simpa only [Category.id_comp] using h
end SerrePositivity.DifferentialGraded
end

end Hom

/-! ## Left（旧 SerrePositivity/DifferentialGraded/Module/Left.lean） -/

/-! # 左dg加群と二重opposite

既存の共変豊穣関手LeftModuleを保持し、Dᵒᵖ上の右加群と比較する。
二重oppositeの合成比較は対称braidingの二乗から得る。
-/

@[expose] public section Left
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 二重oppositeでは二つのKoszul交換が打ち消し合う。 -/
lemma doubleOpposite_composition (x y z : D) :
    eComp (Complex A) (op (op x)) (op (op y)) (op (op z)) =
      eComp (Complex A) x y z := by
  rw [eComp_op_eq, eComp_op_eq]
  change (β_ (x ⟶[Complex A] y) (y ⟶[Complex A] z)).hom ≫
    (β_ (y ⟶[Complex A] z) (x ⟶[Complex A] y)).hom ≫ eComp (Complex A) x y z = _
  rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

/-- Dから二重oppositeへの恒等Homを持つdg関手。 -/
def dgDoubleOpposite : DGFunctor A D Dᵒᵖᵒᵖ where
  obj x := op (op x)
  map _ _ := 𝟙 _
  map_id _ := Category.comp_id _
  map_comp x y z := by
    simp [doubleOpposite_composition]

/-- 二重oppositeからDへの恒等Homを持つdg関手。 -/
def dgDoubleUnop : DGFunctor A Dᵒᵖᵒᵖ D where
  obj x := x.unop.unop
  map _ _ := 𝟙 _
  map_id _ := Category.comp_id _
  map_comp x y z := by
    simpa using
      doubleOpposite_composition A D x.unop.unop y.unop.unop z.unop.unop

namespace LeftModule
variable {A D}

/-- 左加群をDᵒᵖ上の右加群として読む。 -/
def toRightOpposite (M : LeftModule A D) : RightModule A Dᵒᵖ :=
  (dgDoubleUnop A D).comp M

/-- Dᵒᵖ上の右加群を元の共変豊穣関手へ戻す。 -/
def ofRightOpposite (M : RightModule A Dᵒᵖ) : LeftModule A D :=
  (dgDoubleOpposite A D).comp M.toFunctor

@[simp] lemma of_toRightOpposite (M : LeftModule A D) :
    ofRightOpposite (toRightOpposite M) = M := by
  apply EnrichedFunctor.ext (Complex A) (fun _ => rfl)
  intro x y
  simp [ofRightOpposite, toRightOpposite, DGFunctor.comp,
    dgDoubleOpposite, dgDoubleUnop, EnrichedFunctor.comp]

@[simp] lemma to_ofRightOpposite (M : RightModule A Dᵒᵖ) :
    toRightOpposite (ofRightOpposite M) = M := by
  apply EnrichedFunctor.ext (Complex A) (fun _ => rfl)
  intro x y
  simp [ofRightOpposite, toRightOpposite, DGFunctor.comp,
    dgDoubleOpposite, dgDoubleUnop, EnrichedFunctor.comp]

end LeftModule

/-- 対象データの比較。射は後続で全次数自然性のHomを使う。 -/
def leftModuleEquivRightOpposite : LeftModule A D ≃ RightModule A Dᵒᵖ where
  toFun := LeftModule.toRightOpposite
  invFun := LeftModule.ofRightOpposite
  left_inv := LeftModule.of_toRightOpposite
  right_inv := LeftModule.to_ofRightOpposite

end SerrePositivity.DifferentialGraded
end

end Left

/-! ## TriangleShiftMap（旧 SerrePositivity/DifferentialGraded/Module/TriangleShiftMap.lean） -/

/-! # shiftした三角形の同型を加法的関手で移す補助構成子 -/

@[expose] public section TriangleShiftMap
universe u₁ u₂ v₁ v₂

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
variable {C : Type u₁} {E : Type u₂} [Category.{v₁} C] [Category.{v₂} E]
  [Preadditive C] [Preadditive E] [HasShift C ℤ] [HasShift E ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [∀ (n : ℤ), (shiftFunctor E n).Additive]

/-- shiftとの比較を含めて、三角形の同型を関手で移す。 -/
def triangleShiftMapIso (F : C ⥤ E) [F.Additive] [F.CommShift ℤ]
    (s : ℤ) (T T' : Triangle C) (e : (Triangle.shiftFunctor C s).obj T ≅ T') :
    (Triangle.shiftFunctor E s).obj (F.mapTriangle.obj T) ≅ F.mapTriangle.obj T' :=
  (F.mapTriangleCommShiftIso s).symm.app T ≪≫ F.mapTriangle.mapIso e

/-- 始域の三角形同型をshiftしてから、指定された比較同型へ合成する。 -/
def triangleShiftIsoTrans (s : ℤ) (T T' T'' : Triangle C) (e : T ≅ T')
    (e' : (Triangle.shiftFunctor C s).obj T' ≅ T'') :
    (Triangle.shiftFunctor C s).obj T ≅ T'' :=
  (Triangle.shiftFunctor C s).mapIso e ≪≫ e'

end SerrePositivity.DifferentialGraded
end

end TriangleShiftMap

/-! ## Representable（旧 SerrePositivity/DifferentialGraded/Module/Representable.lean） -/

/-! # 右代表 dg 加群

R_x(y)=Hom_D(y,x)。作用は豊穣合成の右tensor転置であり、全斉次射に作用する。
-/

@[expose] public section Representable
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex Opposite
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 代表右加群の Hom chain map。豊穣順の合成を右tensorで転置する。 -/
def representableMap (x : D) (y z : Dᵒᵖ) :
    (y ⟶[Complex A] z) ⟶ homComplex A (y.unop ⟶[Complex A] x) (z.unop ⟶[Complex A] x) :=
  curryRight (eComp (Complex A) z.unop y.unop x)

/-- 代表加群の作用の斉次公式。通常順では (-1)^(pk) が付く。 -/
lemma representableMap_apply (x : D) (y z : Dᵒᵖ) (p k n : ℤ) (hn : k + p = n)
    (f : GradedHom A y z p) (h : GradedHom A y.unop x k) :
    ((representableMap A x y z).f p f).v k n hn h =
      forward A (x := z.unop) (y := y.unop) (z := x) f h (by omega) := rfl

/-- 代表加群の閉単位の保存。 -/
lemma representableMap_id (x : D) (y : Dᵒᵖ) :
    eId (Complex A) y ≫ representableMap A x y y =
      identity (y.unop ⟶[Complex A] x) := by
  apply (unitCycleEquiv (homComplex A (y.unop ⟶[Complex A] x)
    (y.unop ⟶[Complex A] x))).injective
  apply Subtype.ext
  change (cycleFromUnit _ (eId (Complex A) y ≫ representableMap A x y y)).val =
    (cycleFromUnit _ (identity (y.unop ⟶[Complex A] x))).val
  rw [cycleFromUnit_postcomp, identity, cycleFromUnit_unitFromCycle]
  change (representableMap A x y y).f 0 (unitElement A y.unop).val =
    Cochain.ofHom (𝟙 (y.unop ⟶[Complex A] x))
  apply Cochain.ext₀
  intro k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro h
  rw [representableMap_apply]
  change forward A (unitElement A y.unop).val h (zero_add k) = h
  exact forward_unit A h

/-- 代表加群の合成の保存。opposite の符号と Ch(A) の豊穣符号が一致する。 -/
lemma representableMap_comp (x : D) (y z w : Dᵒᵖ) :
    eComp (Complex A) y z w ≫ representableMap A x y w =
      (representableMap A x y z ⊗ₘ representableMap A x z w) ≫
        enrichedComposition (y.unop ⟶[Complex A] x) (z.unop ⟶[Complex A] x)
          (w.unop ⟶[Complex A] x) := by
  apply tensorHom_ext
  intro p q m hm
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f g
  change (representableMap A x y w).f m (forward A f g hm) = _
  rw [opposite_forward A D y z w p q m hm f g]
  simp only [Units.smul_def, map_zsmul]
  -- Evaluate the right-hand tensor map before comparing cochains.
  change (p * q).negOnePow •
    (representableMap A x y w).f m (forward A (x := w.unop) (y := z.unop) (z := y.unop)
      g f (by omega)) =
    (enrichedComposition _ _ _).f m
      (((representableMap A x y z) ⊗ₘ (representableMap A x z w)).f m
        (ιTensorObj (y ⟶[Complex A] z) (z ⟶[Complex A] w) p q m hm (f ⊗ₜ[A] g)))
  rw [tensorMap_apply, enrichedComposition_apply]
  apply Cochain.ext
  intro k n hkn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro h
  change ((p * q).negOnePow •
    ((representableMap A x y w).f m (forward A (x := w.unop) (y := z.unop) (z := y.unop)
      g f (by omega)))).v k n hkn h = _
  rw [Cochain.units_smul_v, Cochain.units_smul_v,
    Cochain.comp_v _ _ hm k (k + p) n rfl (by omega)]
  change (p * q).negOnePow • forward A (x := w.unop) (y := y.unop) (z := x)
      (forward A (x := w.unop) (y := z.unop) (z := y.unop) g f (by omega)) h (by omega) =
    (p * q).negOnePow • forward A (x := w.unop) (y := z.unop) (z := x) g
      (forward A (x := z.unop) (y := y.unop) (z := x) f h (by omega)) (by omega)
  exact congrArg (fun z => (p * q).negOnePow • z)
    (forward_assoc_of_sum A (w := w.unop) (x := z.unop) (y := y.unop) (z := x)
      g f h (a := m) (b := k + p) (by omega) (by omega) (by omega))

/-- 右代表 dg 加群。豊穣関手の単位・合成法則を上で証明する。 -/
abbrev representable (x : D) : RightModule A D where
  obj y := y.unop ⟶[Complex A] x
  map := representableMap A x
  map_id := representableMap_id A x
  map_comp := representableMap_comp A x
end SerrePositivity.DifferentialGraded
end

end Representable

/-! ## Action（旧 SerrePositivity/DifferentialGraded/Module/Action.lean） -/

/-! # 右 dg 加群の斉次作用と全次数自然性 -/

@[expose] public section Action
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex Opposite
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 豊穣 Hom 射を評価する右加群の斉次作用。 -/
def moduleAction (M : RightModule A D) {x y : Dᵒᵖ} {p q n : ℤ}
    (f : GradedHom A x y p) (v : (M.obj x).X q) (hn : q + p = n) : (M.obj y).X n :=
  ((M.map x y).f p f).v q n hn v

/-- 右作用の単位則。 -/
lemma moduleAction_unit (M : RightModule A D) (x : Dᵒᵖ) (q : ℤ) (v : (M.obj x).X q) :
    moduleAction A M (unitElement A x).val v (add_zero q) = v := by
  have h := congrArg (fun f => (cycleFromUnit _ f).val) (M.toFunctor.map_id x)
  rw [cycleFromUnit_postcomp] at h
  change (M.map x x).f 0 (unitElement A x).val =
    (cycleFromUnit _ (identity (M.obj x))).val at h
  rw [identity, cycleFromUnit_unitFromCycle] at h
  unfold moduleAction
  rw [h]
  rfl

/-- 作用は豊穣順の合成に対して Koszul 符号付きで結合する。 -/
lemma moduleAction_forward (M : RightModule A D) {x y z : Dᵒᵖ} {p q r m n s : ℤ}
    (f : GradedHom A x y p) (g : GradedHom A y z q) (v : (M.obj x).X r)
    (hm : p + q = m) (hs : r + p = s) (hn : r + m = n) :
    moduleAction A M (forward A f g hm) v hn = (p * q).negOnePow •
      moduleAction A M g (moduleAction A M f v hs) (by omega) := by
  have h := M.toFunctor.map_comp x y z
  have hh := congrArg (fun l => l.f m
    (ιTensorObj (x ⟶[Complex A] y) (y ⟶[Complex A] z) p q m hm (f ⊗ₜ[A] g))) h
  change (M.map x z).f m (forward A f g hm) = _ at hh
  change (M.map x z).f m (forward A f g hm) =
    (enrichedComposition _ _ _).f m
      (((M.map x y) ⊗ₘ (M.map y z)).f m
        (ιTensorObj (x ⟶[Complex A] y) (y ⟶[Complex A] z) p q m hm (f ⊗ₜ[A] g))) at hh
  rw [tensorMap_apply, enrichedComposition_apply] at hh
  unfold moduleAction
  rw [hh, Cochain.units_smul_v, Cochain.comp_v _ _ hm r s n hs (by omega)]
  rfl

/-- 全次数自然性の成分公式。通常の閉零射だけに課す条件より強い。 -/
lemma moduleParamNaturality_apply {K : Complex A} {M N : RightModule A D}
    (σ : ∀ x : Dᵒᵖ, K ⟶ homComplex A (M.obj x) (N.obj x))
    (h : ∀ x y : Dᵒᵖ, (β_ K (x ⟶[Complex A] y)).hom ≫
      (M.map x y ⊗ₘ σ y) ≫ enrichedComposition _ _ _ =
        (σ x ⊗ₘ N.map x y) ≫ enrichedComposition _ _ _)
    {x y : Dᵒᵖ} {k p r m n : ℤ}
    (t : K.X k) (f : GradedHom A x y p) (v : (M.obj x).X r)
    (hm : k + p = m) (hn : r + m = n) :
    ((σ y).f k t).v (r + p) n (by omega) (moduleAction A M f v rfl) =
      (k * p).negOnePow • moduleAction A N f
        (((σ x).f k t).v r (r + k) rfl v) (by omega) := by
  have hh := congrArg (fun l => l.f m
    (ιTensorObj K (x ⟶[Complex A] y) k p m hm (t ⊗ₜ[A] f))) (h x y)
  change (enrichedComposition _ _ _).f m
    (((M.map x y) ⊗ₘ (σ y)).f m
      ((signedSwap K (x ⟶[Complex A] y)).hom.f m
        (ιTensorObj K (x ⟶[Complex A] y) k p m hm (t ⊗ₜ[A] f)))) =
    (enrichedComposition _ _ _).f m
      (((σ x) ⊗ₘ (N.map x y)).f m
        (ιTensorObj K (x ⟶[Complex A] y) k p m hm (t ⊗ₜ[A] f))) at hh
  rw [signedSwap_apply] at hh
  simp only [Units.smul_def, map_zsmul] at hh
  change (k * p).negOnePow • (enrichedComposition _ _ _).f m
      (((M.map x y) ⊗ₘ (σ y)).f m
        (ιTensorObj (x ⟶[Complex A] y) K p k m (by omega) (f ⊗ₜ[A] t))) = _ at hh
  simp only [tensorMap_apply, enrichedComposition_apply] at hh
  rw [mul_comm p k, smul_smul, Int.units_mul_self, one_smul] at hh
  have hv := congrArg (fun c => c.v r n hn v) hh
  rw [Cochain.units_smul_v,
    Cochain.comp_v _ _ (by omega) r (r + p) n rfl (by omega),
    Cochain.comp_v _ _ hm r (r + k) n rfl (by omega)] at hv
  exact hv
/-- 中間次数を指定して自然性の成分公式を使う。 -/
lemma moduleParamNaturality_apply_of_sum {K : Complex A} {M N : RightModule A D}
    (σ : ∀ x : Dᵒᵖ, K ⟶ homComplex A (M.obj x) (N.obj x))
    (h : ∀ x y : Dᵒᵖ, (β_ K (x ⟶[Complex A] y)).hom ≫
      (M.map x y ⊗ₘ σ y) ≫ enrichedComposition _ _ _ =
        (σ x ⊗ₘ N.map x y) ≫ enrichedComposition _ _ _)
    {x y : Dᵒᵖ} {k p r m n s l : ℤ}
    (t : K.X k) (f : GradedHom A x y p) (v : (M.obj x).X r)
    (hm : k + p = m) (hn : r + m = n) (hs : r + p = s) (hl : r + k = l) :
    ((σ y).f k t).v s n (by omega) (moduleAction A M f v hs) =
      (k * p).negOnePow • moduleAction A N f
        (((σ x).f k t).v r l hl v) (by omega) := by
  subst s l
  exact moduleParamNaturality_apply A σ h t f v hm hn

/-- 全斉次成分の符号付き作用公式から全豊穣自然性を復元する。 -/
lemma moduleParamNaturality_of_apply {K : Complex A} {M N : RightModule A D}
    (σ : ∀ x : Dᵒᵖ, K ⟶ homComplex A (M.obj x) (N.obj x))
    (h : ∀ (x y : Dᵒᵖ) (k p r n : ℤ) (hn : r + (k + p) = n)
      (t : K.X k) (f : GradedHom A x y p) (v : (M.obj x).X r),
      ((σ y).f k t).v (r + p) n (by omega) (moduleAction A M f v rfl) =
        (k * p).negOnePow • moduleAction A N f
          (((σ x).f k t).v r (r + k) rfl v) (by omega)) (x y : Dᵒᵖ) :
    (β_ K (x ⟶[Complex A] y)).hom ≫
      (M.map x y ⊗ₘ σ y) ≫ enrichedComposition _ _ _ =
        (σ x ⊗ₘ N.map x y) ≫ enrichedComposition _ _ _ := by
  apply tensorHom_ext
  intro k p m hm
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro t f
  change (enrichedComposition _ _ _).f m
    (((M.map x y) ⊗ₘ σ y).f m
      ((signedSwap K (x ⟶[Complex A] y)).hom.f m
        (ιTensorObj K (x ⟶[Complex A] y) k p m hm (t ⊗ₜ[A] f)))) =
    (enrichedComposition _ _ _).f m
      (((σ x) ⊗ₘ N.map x y).f m
        (ιTensorObj K (x ⟶[Complex A] y) k p m hm (t ⊗ₜ[A] f)))
  rw [signedSwap_apply]
  simp only [Units.smul_def, map_zsmul]
  change (k * p).negOnePow • (enrichedComposition _ _ _).f m
      (((M.map x y) ⊗ₘ σ y).f m
        (ιTensorObj (x ⟶[Complex A] y) K p k m (by omega) (f ⊗ₜ[A] t))) = _
  rw [tensorMap_apply, tensorMap_apply, enrichedComposition_apply,
    enrichedComposition_apply, mul_comm p k, smul_smul,
    Int.units_mul_self, one_smul]
  apply Cochain.ext
  intro r n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  rw [Cochain.units_smul_v,
    Cochain.comp_v _ _ (by omega) r (r + p) n rfl (by omega),
    Cochain.comp_v _ _ hm r (r + k) n rfl (by omega)]
  exact h x y k p r n (by omega) t f v

/-- Mathlib パラメータ付き自然変換の符号付き作用公式。 -/
lemma moduleParamTrans_apply {K : Complex A} {M N : RightModule A D}
    (τ : ModuleParamTrans A D K M N) {x y : Dᵒᵖ} {k p r m n : ℤ}
    (t : K.X k) (f : GradedHom A x y p) (v : (M.obj x).X r)
    (hm : k + p = m) (hn : r + m = n) :
    ((τ.app y).f k t).v (r + p) n (by omega) (moduleAction A M f v rfl) =
      (k * p).negOnePow • moduleAction A N f
        (((τ.app x).f k t).v r (r + k) rfl v) (by omega) :=
  moduleParamNaturality_apply A τ.app τ.naturality t f v hm hn
/-- 全斉次射の cochain 合成の可換式からパラメータ付き自然性を復元する。 -/
lemma moduleParamNaturality_of_cochain {K : Complex A} {M N : RightModule A D}
    (σ : ∀ x : Dᵒᵖ, K ⟶ homComplex A (M.obj x) (N.obj x))
    (h : ∀ (x y : Dᵒᵖ) (k p m : ℤ) (hm : k + p = m)
      (t : K.X k) (f : GradedHom A x y p),
      ((M.map x y).f p f).comp ((σ y).f k t) (by omega) =
        (k * p).negOnePow • (((σ x).f k t).comp ((N.map x y).f p f) hm))
    (x y : Dᵒᵖ) :
    (β_ K (x ⟶[Complex A] y)).hom ≫
      (M.map x y ⊗ₘ σ y) ≫ enrichedComposition _ _ _ =
        (σ x ⊗ₘ N.map x y) ≫ enrichedComposition _ _ _ := by
  apply tensorHom_ext
  intro k p m hm
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro t f
  change (enrichedComposition _ _ _).f m
    ((M.map x y ⊗ₘ σ y).f m
      ((signedSwap K (x ⟶[Complex A] y)).hom.f m
        (ιTensorObj K (x ⟶[Complex A] y) k p m hm (t ⊗ₜ[A] f)))) =
    (enrichedComposition _ _ _).f m
      ((σ x ⊗ₘ N.map x y).f m
        (ιTensorObj K (x ⟶[Complex A] y) k p m hm (t ⊗ₜ[A] f)))
  rw [signedSwap_apply]
  simp only [Units.smul_def, map_zsmul]
  change (k * p).negOnePow • (enrichedComposition _ _ _).f m
    ((M.map x y ⊗ₘ σ y).f m
      (ιTensorObj (x ⟶[Complex A] y) K p k m (by omega) (f ⊗ₜ[A] t))) = _
  rw [tensorMap_apply, tensorMap_apply, enrichedComposition_apply,
    enrichedComposition_apply, mul_comm p k, smul_smul, Int.units_mul_self, one_smul]
  exact h x y k p m hm t f
end SerrePositivity.DifferentialGraded
end

end Action

/-! ## Yoneda（旧 SerrePositivity/DifferentialGraded/Module/Yoneda.lean） -/

/-! # 右代表 dg 加群の全次数 Yoneda -/

@[expose] public section Yoneda
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex Opposite
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 値 K→M(x) から代表加群の Hom 族への chain map を作る。 -/
def yonedaExtensionApp (x : D) (M : RightModule A D) {K : Complex A}
    (ψ : K ⟶ M.obj (op x)) (y : Dᵒᵖ) :
    K ⟶ homComplex A ((representable A x).obj y) (M.obj y) :=
  curryRight ((ψ ⊗ₘ M.map (op x) y) ≫ evaluation (M.obj (op x)) (M.obj y))

/-- Yoneda 拡張の斉次公式。左 tensor 評価の Koszul 符号を保持する。 -/
lemma yonedaExtensionApp_apply (x : D) (M : RightModule A D) {K : Complex A}
    (ψ : K ⟶ M.obj (op x)) (y : Dᵒᵖ) (k q n : ℤ) (hn : q + k = n)
    (t : K.X k) (h : GradedHom A y.unop x q) :
    ((yonedaExtensionApp A x M ψ y).f k t).v q n hn h =
      (k * q).negOnePow • moduleAction A M (x := op x) (y := y) h
        (ψ.f k t) (by omega) := by
  change (evaluation _ _).f n
    ((ψ ⊗ₘ M.map (op x) y).f n
      (ιTensorObj K (op x ⟶[Complex A] y) k q n (by omega) (t ⊗ₜ[A] h))) = _
  rw [tensorMap_apply, evaluation_apply]
  rfl

/-- 右代表の作用と加群作用の整合性。二つの opposite 符号が消える。 -/
lemma moduleAction_representable (x : D) (M : RightModule A D) (y z : Dᵒᵖ)
    (p q k m n s : ℤ) (hm : q + p = m) (hs : k + q = s) (hn : k + m = n)
    (f : GradedHom A y z p) (h : GradedHom A y.unop x q)
    (t : (M.obj (op x)).X k) :
    moduleAction A M (x := op x) (y := z)
      (moduleAction A (representable A x) f h hm) t hn =
    moduleAction A M f (moduleAction A M (x := op x) (y := y) h t hs) (by omega) := by
  change moduleAction A M (x := op x) (y := z)
    (forward A (x := z.unop) (y := y.unop) (z := x) f h (by omega)) t hn = _
  have ho := opposite_forward A D (op x) y z q p m hm h f
  have he := moduleAction_forward A M (x := op x) (y := y) (z := z)
    h f t hm hs hn
  rw [ho] at he
  unfold moduleAction at he ⊢
  simp only [Units.smul_def, map_zsmul] at he
  change (q * p).negOnePow •
    (((M.map (op x) z).f m
      (forward A (x := z.unop) (y := y.unop) (z := x) f h (by omega))).v k n hn t) =
    (q * p).negOnePow • _ at he
  exact smul_left_cancel (q * p).negOnePow he

/-- Yoneda 拡張は全豊穣 Hom に対して自然。 -/
lemma yonedaExtensionApp_naturality (x : D) (M : RightModule A D) {K : Complex A}
    (ψ : K ⟶ M.obj (op x)) (y z : Dᵒᵖ) :
    (β_ K (y ⟶[Complex A] z)).hom ≫
      ((representable A x).map y z ⊗ₘ yonedaExtensionApp A x M ψ z) ≫
        enrichedComposition _ _ _ =
      (yonedaExtensionApp A x M ψ y ⊗ₘ M.map y z) ≫ enrichedComposition _ _ _ := by
  apply moduleParamNaturality_of_apply
  intro y z k p q n hn t f h
  rw [yonedaExtensionApp_apply, yonedaExtensionApp_apply]
  change (k * (q + p)).negOnePow •
    moduleAction A M (x := op x) (y := z)
      (moduleAction A (representable A x) f h rfl) (ψ.f k t) (by omega) =
    (k * p).negOnePow • moduleAction A M f
      ((k * q).negOnePow • moduleAction A M (x := op x) (y := y) h (ψ.f k t)
        (by omega)) (by omega)
  have hx := moduleAction_representable A x M y z p q k (q + p) n (q + k)
    rfl (by omega) (by omega) f h (ψ.f k t)
  calc
    _ = (k * (q + p)).negOnePow •
        moduleAction A M f (moduleAction A M (x := op x) (y := y) h
          (ψ.f k t) (by omega)) (by omega) := congrArg (fun v => (k * (q + p)).negOnePow • v) hx
    _ = _ := by
      have hs : (k * (q + p)).negOnePow =
          (k * p).negOnePow * (k * q).negOnePow := by
        rw [← Int.negOnePow_add]
        congr 1
        ring
      rw [hs]
      unfold moduleAction
      simp only [Units.smul_def, map_zsmul, smul_smul, Units.val_mul]

/-- K パラメータ付き Yoneda 拡張。 -/
def yonedaExtension (x : D) (M : RightModule A D) {K : Complex A}
    (ψ : K ⟶ M.obj (op x)) : ModuleParamTrans A D K (representable A x) M where
  app := yonedaExtensionApp A x M ψ
  naturality := yonedaExtensionApp_naturality A x M ψ
/-- 代表の単位元で自然変換の成分族を評価する chain map。 -/
def yonedaEvaluateFamily (x : D) (M : RightModule A D) {K : Complex A}
    (σ : ∀ y : Dᵒᵖ, K ⟶ homComplex A ((representable A x).obj y) (M.obj y)) :
    K ⟶ M.obj (op x) :=
  (ρ_ K).inv ≫ (𝟙 K ⊗ₘ eId (Complex A) x) ≫ uncurryRight (σ (op x))

/-- 単位元での評価の全次数公式。 -/
lemma yonedaEvaluateFamily_apply (x : D) (M : RightModule A D) {K : Complex A}
    (σ : ∀ y : Dᵒᵖ, K ⟶ homComplex A ((representable A x).obj y) (M.obj y))
    (k : ℤ) (t : K.X k) :
    (yonedaEvaluateFamily A x M σ).f k t =
      ((σ (op x)).f k t).v 0 k (by omega) (unitElement A x).val := by
  have hv := congr($(rightUnitor'_inv K k).hom t)
  change (ρ_ K).inv.f k t =
    ιTensorObj K (𝟙_ (Complex A)) k 0 k (add_zero k) (t ⊗ₜ[A] (1 : A)) at hv
  change (uncurryRight (σ (op x))).f k
    ((𝟙 K ⊗ₘ eId (Complex A) x).f k ((ρ_ K).inv.f k t)) = _
  rw [hv, tensorMap_apply, uncurryRight_apply]
  rfl

/-- Yoneda 拡張を単位元で評価すると元の値に戻る。 -/
lemma yonedaEvaluate_extension (x : D) (M : RightModule A D) {K : Complex A}
    (ψ : K ⟶ M.obj (op x)) :
    yonedaEvaluateFamily A x M (yonedaExtensionApp A x M ψ) = ψ := by
  apply HomologicalComplex.Hom.ext
  funext k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  rw [yonedaEvaluateFamily_apply, yonedaExtensionApp_apply]
  simp only [mul_zero, Int.negOnePow_zero, one_smul]
  exact moduleAction_unit A M (op x) k (ψ.f k t)

/-- 全次数自然性を持つ成分族は単位での評価から復元できる。 -/
lemma yonedaExtensionApp_restore (x : D) (M : RightModule A D) {K : Complex A}
    (σ : ∀ y : Dᵒᵖ, K ⟶ homComplex A ((representable A x).obj y) (M.obj y))
    (hnat : ∀ y z : Dᵒᵖ, (β_ K (y ⟶[Complex A] z)).hom ≫
      ((representable A x).map y z ⊗ₘ σ z) ≫ enrichedComposition _ _ _ =
        (σ y ⊗ₘ M.map y z) ≫ enrichedComposition _ _ _) (y : Dᵒᵖ) :
    yonedaExtensionApp A x M (yonedaEvaluateFamily A x M σ) y = σ y := by
  apply HomologicalComplex.Hom.ext
  funext k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  apply Cochain.ext
  intro q n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro h
  change ((yonedaExtensionApp A x M (yonedaEvaluateFamily A x M σ) y).f k t).v
    q n hn h = _
  rw [yonedaExtensionApp_apply, yonedaEvaluateFamily_apply]
  have he := moduleParamNaturality_apply_of_sum A σ hnat
    (x := op x) (y := y) (r := 0)
    (m := k + q) (n := n) (s := q) (l := k)
    t h (unitElement A x).val rfl (by omega) (zero_add q) (zero_add k)
  change ((σ y).f k t).v q n hn
      (forward A (x := y.unop) (y := x) (z := x) h (unitElement A x).val
        (add_zero q)) = _ at he
  rw [unit_forward A h] at he
  exact he.symm


/-- 全次数自然変換は単位元での値から復元できる。 -/
lemma yonedaExtension_evaluate (x : D) (M : RightModule A D) {K : Complex A}
    (τ : ModuleParamTrans A D K (representable A x) M) :
    yonedaExtension A x M (yonedaEvaluateFamily A x M τ.app) = τ := by
  apply GradedNatTrans.ext
  funext y
  exact yonedaExtensionApp_restore A x M τ.app τ.naturality y

/-- 任意パラメータ複体での全次数 dg Yoneda 同値。 -/
def dgYonedaEquiv (x : D) (M : RightModule A D) (K : Complex A) :
    ModuleParamTrans A D K (representable A x) M ≃ (K ⟶ M.obj (op x)) where
  toFun τ := yonedaEvaluateFamily A x M τ.app
  invFun := yonedaExtension A x M
  left_inv := yonedaExtension_evaluate A x M
  right_inv := yonedaEvaluate_extension A x M
/-- Yoneda 拡張はパラメータ複体の射での前合成と可換。 -/
lemma yonedaExtensionApp_precomp (x : D) (M : RightModule A D) {K L : Complex A}
    (g : L ⟶ K) (ψ : K ⟶ M.obj (op x)) (y : Dᵒᵖ) :
    yonedaExtensionApp A x M (g ≫ ψ) y = g ≫ yonedaExtensionApp A x M ψ y := by
  dsimp only [yonedaExtensionApp]
  rw [← curryRight_naturality_source, tensorHom_comp_tensorHom_assoc]
  simp

/-- 単位での評価はパラメータ複体の射での前合成と可換。 -/
lemma yonedaEvaluateFamily_precomp (x : D) (M : RightModule A D) {K L : Complex A}
    (g : L ⟶ K)
    (σ : ∀ y : Dᵒᵖ, K ⟶ homComplex A ((representable A x).obj y) (M.obj y)) :
    yonedaEvaluateFamily A x M (fun y => g ≫ σ y) = g ≫ yonedaEvaluateFamily A x M σ := by
  apply HomologicalComplex.Hom.ext
  funext k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  rw [yonedaEvaluateFamily_apply]
  change ((σ (op x)).f k (g.f k t)).v 0 k (by omega) (unitElement A x).val =
    (yonedaEvaluateFamily A x M σ).f k (g.f k t)
  rw [yonedaEvaluateFamily_apply]

/-- dg Yoneda の Hom 複体そのものの同型。H⁰ のみの同値ではない。 -/
def dgYonedaIso [Small.{u} D] (x : D) (M : RightModule A D) :
    moduleHom A D (representable A x) M ≅ M.obj (op x) where
  hom := yonedaEvaluateFamily A x M
    (fun y => moduleHomπ A D (representable A x) M y.unop)
  inv := (moduleHomEquiv A D (M.obj (op x)) (representable A x) M).symm
    (yonedaExtension A x M (𝟙 _))
  hom_inv_id := by
    apply moduleHom_ext
    intro y
    rw [Category.assoc, moduleHomEquiv_symm_π]
    change _ ≫ yonedaExtensionApp A x M (𝟙 _) (op y) = _
    rw [← yonedaExtensionApp_precomp]
    simp only [Category.comp_id]
    have hr := yonedaExtensionApp_restore A x M
      (fun y => moduleHomπ A D (representable A x) M y.unop)
      (moduleHomπ_naturality A D (representable A x) M) (op y)
    exact hr
  inv_hom_id := by
    rw [← yonedaEvaluateFamily_precomp]
    have hp : ∀ y : Dᵒᵖ,
        (moduleHomEquiv A D (M.obj (op x)) (representable A x) M).symm
          (yonedaExtension A x M (𝟙 _)) ≫ moduleHomπ A D (representable A x) M y.unop =
        yonedaExtensionApp A x M (𝟙 _) y := by
      intro y
      exact moduleHomEquiv_symm_π A D _ _ _ _ _
    simp_rw [hp]
    exact yonedaEvaluate_extension A x M (𝟙 _)
end SerrePositivity.DifferentialGraded
end

end Yoneda

/-! ## Tensor（旧 SerrePositivity/DifferentialGraded/Module/Tensor.lean） -/

/-! # 右 dg 加群の左 tensor と自由加群の対象

作用は左 tensor の豊穣関手との合成で構成する。
通常の閉零関手への置換をせず、全次数の作用・単位・合成を保持する。
-/

@[expose] public section Tensor
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex Opposite
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 右加群 M の値に非有界複体 K を左 tensor する。 -/
abbrev tensorModule (K : Complex A) (M : RightModule A D) : RightModule A D where
  obj x := K ⊗ M.obj x
  map x y := M.map x y ≫ tensorLeftHom K (M.obj x) (M.obj y)
  map_id := (DGFunctor.comp M.toFunctor (tensorLeftDG K)).map_id
  map_comp := (DGFunctor.comp M.toFunctor (tensorLeftDG K)).map_comp

/-- tensor 加群は既存豊穣関手の合成と定義上同じデータ。 -/
lemma tensorModule_eq_comp (K : Complex A) (M : RightModule A D) :
    (tensorModule K M).toFunctor = DGFunctor.comp M.toFunctor (tensorLeftDG K) := rfl

/-- tensor 加群の斉次右作用。射の次数 p が K の次数 i を越える符号。 -/
lemma tensorModule_action (K : Complex A) (M : RightModule A D) (x y : Dᵒᵖ)
    (p i j a b n : ℤ) (ha : i + j = a) (hb : j + p = b) (hn : a + p = n)
    (f : GradedHom A x y p) (t : K.X i) (v : (M.obj x).X j) :
    moduleAction A (tensorModule K M) f
      (ιTensorObj K (M.obj x) i j a ha (t ⊗ₜ[A] v)) hn =
    (p * i).negOnePow • ιTensorObj K (M.obj y) i b n (by omega)
      (t ⊗ₜ[A] moduleAction A M f v hb) := by
  change ((tensorLeftHom K (M.obj x) (M.obj y)).f p ((M.map x y).f p f)).v a n hn
    (ιTensorObj K (M.obj x) i j a ha (t ⊗ₜ[A] v)) = _
  exact tensorLeftHom_apply_of_sum K (M.obj x) (M.obj y) p i j a b n ha hb hn _ t v

/-- x において複体 K で生成される自由右加群の対象。 -/
abbrev freeModule (x : D) (K : Complex A) : RightModule A D :=
  tensorModule K (representable A x)

/-- 自由加群の値は K⊗Hom_D(y,x)。 -/
lemma freeModule_obj (x y : D) (K : Complex A) :
    (freeModule x K).obj (op y) = K ⊗ (y ⟶[Complex A] x) := rfl
end SerrePositivity.DifferentialGraded
end

end Tensor

/-! ## LeftAction（旧 SerrePositivity/DifferentialGraded/Module/LeftAction.lean） -/

/-! # 左dg加群の全次数作用

共変豊穣関手のHom射を評価する。豊穣順合成と通常順合成のKoszul規約を保持する。
-/

@[expose] public section LeftAction
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex Opposite
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 豊穣 Hom 射を評価する左加群の斉次作用。 -/
def leftAction (M : LeftModule A D) {x y : D} {p q n : ℤ}
    (f : GradedHom A x y p) (v : (M.obj x).X q) (hn : q + p = n) : (M.obj y).X n :=
  ((M.map x y).f p f).v q n hn v

/-- 左作用の単位則。 -/
lemma leftAction_unit (M : LeftModule A D) (x : D) (q : ℤ) (v : (M.obj x).X q) :
    leftAction A M (unitElement A x).val v (add_zero q) = v := by
  have h := congrArg (fun f => (cycleFromUnit _ f).val) (M.map_id x)
  rw [cycleFromUnit_postcomp] at h
  change (M.map x x).f 0 (unitElement A x).val =
    (cycleFromUnit _ (identity (M.obj x))).val at h
  rw [identity, cycleFromUnit_unitFromCycle] at h
  unfold leftAction
  rw [h]
  rfl

/-- 作用は豊穣順の合成に対して Koszul 符号付きで結合する。 -/
lemma leftAction_forward (M : LeftModule A D) {x y z : D} {p q r m n s : ℤ}
    (f : GradedHom A x y p) (g : GradedHom A y z q) (v : (M.obj x).X r)
    (hm : p + q = m) (hs : r + p = s) (hn : r + m = n) :
    leftAction A M (forward A f g hm) v hn = (p * q).negOnePow •
      leftAction A M g (leftAction A M f v hs) (by omega) := by
  have h := M.map_comp x y z
  have hh := congrArg (fun l => l.f m
    (ιTensorObj (x ⟶[Complex A] y) (y ⟶[Complex A] z) p q m hm (f ⊗ₜ[A] g))) h
  change (M.map x z).f m (forward A f g hm) = _ at hh
  change (M.map x z).f m (forward A f g hm) =
    (enrichedComposition _ _ _).f m
      (((M.map x y) ⊗ₘ (M.map y z)).f m
        (ιTensorObj (x ⟶[Complex A] y) (y ⟶[Complex A] z) p q m hm (f ⊗ₜ[A] g))) at hh
  rw [tensorMap_apply] at hh
  change (M.map x z).f m (forward A f g hm) =
    (enrichedComposition _ _ _).f m
      (ιTensorObj (homComplex A (M.obj x) (M.obj y))
        (homComplex A (M.obj y) (M.obj z)) p q m hm
          (((M.map x y).f p f) ⊗ₜ[A] ((M.map y z).f q g))) at hh
  rw [enrichedComposition_apply] at hh
  unfold leftAction
  rw [hh, Cochain.units_smul_v, Cochain.comp_v _ _ hm r s n hs (by omega)]
  rfl

end SerrePositivity.DifferentialGraded
end

end LeftAction

/-! ## LeftActionComparison（旧 SerrePositivity/DifferentialGraded/Module/LeftActionComparison.lean） -/

/-! # opposite表示の作用と元の左右作用 -/

@[expose] public section LeftActionComparison
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

lemma leftToRightOpposite_action (N : LeftModule A D) {x y : D} {p r n : ℤ}
    (f : GradedHom A x y p) (v : (N.obj x).X r) (hn : r + p = n) :
    moduleAction A N.toRightOpposite (x := op (op x)) (y := op (op y)) f v hn =
      leftAction A N f v hn := by
  change (((𝟙 _ ≫ N.map x y).f p f).v r n hn) v = _
  rw [Category.id_comp]
  rfl

lemma rightToLeft_action (M : RightModule A D) {x y : Dᵒᵖ} {p r n : ℤ}
    (f : GradedHom A x y p) (v : (M.obj x).X r) (hn : r + p = n) :
    leftAction A M.toFunctor f v hn = moduleAction A M f v hn := rfl

end SerrePositivity.DifferentialGraded
end

end LeftActionComparison

/-! ## LeftRepresentable（旧 SerrePositivity/DifferentialGraded/Module/LeftRepresentable.lean） -/

/-! # 共変representable左dg加群 -/

@[expose] public section LeftRepresentable
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- xにおける値がD(z,x)である共変representable。 -/
def leftRepresentable (z : D) : LeftModule A D :=
  LeftModule.ofRightOpposite (representable A (op z))

lemma leftRepresentable_action (z x y : D) {p q n : ℤ}
    (f : GradedHom A x y p) (h : GradedHom A z x q) (hn : q + p = n) :
    leftAction A (leftRepresentable A z) f h hn =
      (p * q).negOnePow • forward A h f hn := by
  change (((𝟙 _ ≫ representableMap A (op z) (op (op x)) (op (op y))).f p f).v q n hn h) = _
  simp only [Category.id_comp]
  change forward A (D := Dᵒᵖ) (x := op y) (y := op x) (z := op z) f h (by omega) = _
  exact opposite_forward A D (op y) (op x) (op z) p q n (by omega) f h

end SerrePositivity.DifferentialGraded
end

end LeftRepresentable

/-! ## HomElements（旧 SerrePositivity/DifferentialGraded/Module/HomElements.lean） -/

/-! # 主Hom endの斉次要素の構成

全次数で自然なcochain族を、diskの生成元とequalizerの普遍性からendへ入れる。
cycle条件は課さない。
-/

@[expose] public section HomElements
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

lemma moduleParamRelationLeft_apply {K : Complex A} {M N : RightModule A D}
    (σ : ∀ x : Dᵒᵖ, K ⟶ homComplex A (M.obj x) (N.obj x))
    (x y : Dᵒᵖ) (k p : ℤ) (t : K.X k) (f : GradedHom A x y p) :
    ((curryRight ((β_ K (x ⟶[Complex A] y)).hom ≫
      (M.map x y ⊗ₘ σ y) ≫ enrichedComposition _ _ _)).f k t).v p (k + p) (by omega) f =
      ((M.map x y).f p f).comp ((σ y).f k t) (by omega : p + k = k + p) := by
  change (enrichedComposition _ _ _).f (k + p)
    ((M.map x y ⊗ₘ σ y).f (k + p)
      ((signedSwap K (x ⟶[Complex A] y)).hom.f (k + p)
        (ιTensorObj K (x ⟶[Complex A] y) k p (k + p) rfl (t ⊗ₜ[A] f)))) = _
  rw [signedSwap_apply]
  simp only [Units.smul_def, map_zsmul]
  change (k * p).negOnePow • (enrichedComposition _ _ _).f (k + p)
    ((M.map x y ⊗ₘ σ y).f (k + p)
      (ιTensorObj (x ⟶[Complex A] y) K p k (k + p) (by omega) (f ⊗ₜ[A] t))) = _
  rw [tensorMap_apply, enrichedComposition_apply, mul_comm p k, smul_smul,
    Int.units_mul_self, one_smul]

lemma moduleParamRelationRight_apply {K : Complex A} {M N : RightModule A D}
    (σ : ∀ x : Dᵒᵖ, K ⟶ homComplex A (M.obj x) (N.obj x))
    (x y : Dᵒᵖ) (k p : ℤ) (t : K.X k) (f : GradedHom A x y p) :
    ((curryRight ((σ x ⊗ₘ N.map x y) ≫ enrichedComposition _ _ _)).f k t).v
        p (k + p) (by omega) f =
      (k * p).negOnePow • (((σ x).f k t).comp ((N.map x y).f p f) rfl) := by
  change (enrichedComposition _ _ _).f (k + p)
    ((σ x ⊗ₘ N.map x y).f (k + p)
      (ιTensorObj K (x ⟶[Complex A] y) k p (k + p) rfl (t ⊗ₜ[A] f))) = _
  rw [tensorMap_apply, enrichedComposition_apply]

abbrev moduleHomDiskFamily {M N : RightModule A D} (q : ℤ)
    (h : ∀ x : Dᵒᵖ, Homogeneous (M.obj x) (N.obj x) q) (x : Dᵒᵖ) :
    complexDisk A q ⟶ homComplex A (M.obj x) (N.obj x) :=
  (complexDiskHomEquiv A _ q).symm (h x)

lemma moduleHomDiskFamily_naturality {M N : RightModule A D} (q : ℤ)
    (h : ∀ x : Dᵒᵖ, Homogeneous (M.obj x) (N.obj x) q)
    (hn : ∀ (x y : Dᵒᵖ) (p : ℤ) (f : GradedHom A x y p),
      ((M.map x y).f p f).comp (h y) (by omega : p + q = q + p) =
        (q * p).negOnePow • ((h x).comp ((N.map x y).f p f) rfl)) (x y : Dᵒᵖ) :
    curryRight ((β_ (complexDisk A q) (x ⟶[Complex A] y)).hom ≫
      (M.map x y ⊗ₘ moduleHomDiskFamily A q h y) ≫ enrichedComposition _ _ _) =
    curryRight ((moduleHomDiskFamily A q h x ⊗ₘ N.map x y) ≫ enrichedComposition _ _ _) := by
  apply (complexDiskHomEquiv A _ q).injective
  rw [complexDiskHomEquiv_apply, complexDiskHomEquiv_apply]
  change (curryRight _).f q ((complexDiskX₀ A q).inv (1 : A)) =
    (curryRight _).f q ((complexDiskX₀ A q).inv (1 : A))
  apply Cochain.ext
  intro p n hpn
  obtain rfl : n = q + p := by omega
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  let σ := fun z : Dᵒᵖ =>
    (complexDiskHomEquiv A (homComplex A (M.obj z) (N.obj z)) q).symm (h z)
  have hL := moduleParamRelationLeft_apply A (M := M) (N := N) σ x y
    q p ((complexDiskX₀ A q).inv (1 : A)) f
  have hR := moduleParamRelationRight_apply A (M := M) (N := N) σ x y
    q p ((complexDiskX₀ A q).inv (1 : A)) f
  have hg (z : Dᵒᵖ) :=
    complexDiskHomEquiv_symm_generator A (homComplex A (M.obj z) (N.obj z)) q (h z)
  refine hL.trans (Eq.trans ?_ hR.symm)
  change ((M.map x y).f p f).comp
      (((complexDiskHomEquiv A (homComplex A (M.obj y) (N.obj y)) q).symm (h y)).f q
        ((complexDiskX₀ A q).inv (1 : A)))
      (by omega : p + q = q + p) =
    (q * p).negOnePow •
      ((((complexDiskHomEquiv A (homComplex A (M.obj x) (N.obj x)) q).symm (h x)).f q
        ((complexDiskX₀ A q).inv (1 : A))).comp
        ((N.map x y).f p f) rfl)
  rw [hg, hg]
  exact hn x y p f

variable (D) [Small.{u} D]

def moduleHomElementFamilyMap {M N : RightModule A D} (q : ℤ)
    (h : ∀ x : Dᵒᵖ, Homogeneous (M.obj x) (N.obj x) q) :
    complexDisk A q ⟶ homCandidates A D M N :=
  Pi.lift (fun x => (complexDiskHomEquiv A (homComplex A (M.obj (op x)) (N.obj (op x))) q).symm
    (h (op x)))

lemma moduleHomElementFamilyMap_condition {M N : RightModule A D} (q : ℤ)
    (h : ∀ x : Dᵒᵖ, Homogeneous (M.obj x) (N.obj x) q)
    (hn : ∀ (x y : Dᵒᵖ) (p : ℤ) (f : GradedHom A x y p),
      ((M.map x y).f p f).comp (h y) (by omega : p + q = q + p) =
        (q * p).negOnePow • ((h x).comp ((N.map x y).f p f) rfl)) :
    moduleHomElementFamilyMap A D q h ≫ homRelationsLeft A D M N =
      moduleHomElementFamilyMap A D q h ≫ homRelationsRight A D M N := by
  apply Pi.hom_ext
  rintro ⟨x, y⟩
  simp only [homRelationsLeft, homRelationsRight, Category.assoc, homRelations, Pi.lift_comp_π]
  rw [← curryRight_naturality_source, ← curryRight_naturality_source,
    homNaturalityLeft_precomp, homNaturalityRight_precomp]
  simp only [moduleHomElementFamilyMap, Pi.lift_comp_π]
  exact moduleHomDiskFamily_naturality A q h hn (op x) (op y)

def moduleHomElementMk {M N : RightModule A D} (q : ℤ)
    (h : ∀ x : Dᵒᵖ, Homogeneous (M.obj x) (N.obj x) q)
    (hn : ∀ (x y : Dᵒᵖ) (p : ℤ) (f : GradedHom A x y p),
      ((M.map x y).f p f).comp (h y) (by omega : p + q = q + p) =
        (q * p).negOnePow • ((h x).comp ((N.map x y).f p f) rfl)) :
    (moduleHom A D M N).X q :=
  complexDiskHomEquiv A _ q
    (equalizer.lift (moduleHomElementFamilyMap A D q h)
      (moduleHomElementFamilyMap_condition A D q h hn))

lemma moduleHomElementMk_π {M N : RightModule A D} (q : ℤ)
    (h : ∀ x : Dᵒᵖ, Homogeneous (M.obj x) (N.obj x) q) (hn) (x : D) :
    (moduleHomπ A D M N x).f q (moduleHomElementMk A D q h hn) = h (op x) := by
  have hp : equalizer.lift (moduleHomElementFamilyMap A D q h)
      (moduleHomElementFamilyMap_condition A D q h hn) ≫ moduleHomπ A D M N x =
    (complexDiskHomEquiv A (homComplex A (M.obj (op x)) (N.obj (op x))) q).symm (h (op x)) := by
    simp only [moduleHomπ, equalizer.lift_ι_assoc, moduleHomElementFamilyMap, Pi.lift_comp_π]
  have he := congrArg (complexDiskHomEquiv A _ q) hp
  rw [complexDiskHomEquiv_naturality, Equiv.apply_symm_apply] at he
  exact he

lemma moduleHomElement_ext {M N : RightModule A D} {q : ℤ}
    {z w : (moduleHom A D M N).X q}
    (h : ∀ x : D, (moduleHomπ A D M N x).f q z = (moduleHomπ A D M N x).f q w) : z = w := by
  apply (complexDiskHomEquiv A (moduleHom A D M N) q).symm.injective
  apply moduleHom_ext
  intro x
  apply (complexDiskHomEquiv A _ q).injective
  rw [complexDiskHomEquiv_naturality, complexDiskHomEquiv_naturality,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact h x

/-- 主Hom endの任意の斉次要素の全次数自然性。 -/
lemma moduleHomElement_naturality {M N : RightModule A D} (q : ℤ)
    (z : (moduleHom A D M N).X q) (x y : Dᵒᵖ) (p : ℤ) (f : GradedHom A x y p) :
    ((M.map x y).f p f).comp ((moduleHomπ A D M N y.unop).f q z)
        (by omega : p + q = q + p) =
      (q * p).negOnePow • (((moduleHomπ A D M N x.unop).f q z).comp
        ((N.map x y).f p f) rfl) := by
  let σ := fun t : Dᵒᵖ => moduleHomπ A D M N t.unop
  have hL := moduleParamRelationLeft_apply A (M := M) (N := N) σ x y q p z f
  have hR := moduleParamRelationRight_apply A (M := M) (N := N) σ x y q p z f
  have hc := congrArg (fun a => (a.f q z).v p (q + p) (by omega) f)
    (congrArg curryRight (moduleHomπ_naturality A D M N x y))
  exact hL.symm.trans (hc.trans hR)

/-- 成分を取り出して再構成すると元の斉次要素を得る。 -/
lemma moduleHomElementMk_components {M N : RightModule A D} (q : ℤ)
    (z : (moduleHom A D M N).X q) :
    moduleHomElementMk A D q (fun x => (moduleHomπ A D M N x.unop).f q z)
      (moduleHomElement_naturality A D q z) = z := by
  apply moduleHomElement_ext A D
  intro x
  exact moduleHomElementMk_π A D q _ _ x

lemma moduleHomElement_d_π {M N : RightModule A D} (q r : ℤ)
    (z : (moduleHom A D M N).X q) (x : D) :
    (moduleHomπ A D M N x).f r ((moduleHom A D M N).d q r z) =
      δ q r ((moduleHomπ A D M N x).f q z) := by
  have h := congrArg (fun a => a z) ((moduleHomπ A D M N x).comm q r)
  exact h.symm

end SerrePositivity.DifferentialGraded
end

end HomElements

/-! ## Composition（旧 SerrePositivity/DifferentialGraded/Module/Composition.lean） -/

/-! # dg 加群のパラメータ付き変換の合成 -/

@[expose] public section Composition
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex Opposite
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- パラメータ付き変換族の対象ごとの豊穣合成。 -/
def moduleComposeApp {K L : Complex A} {M N P : RightModule A D}
    (a : ∀ x : Dᵒᵖ, K ⟶ homComplex A (M.obj x) (N.obj x))
    (b : ∀ x : Dᵒᵖ, L ⟶ homComplex A (N.obj x) (P.obj x)) (x : Dᵒᵖ) :
    K ⊗ L ⟶ homComplex A (M.obj x) (P.obj x) :=
  (a x ⊗ₘ b x) ≫ enrichedComposition _ _ _

/-- パラメータ合成の斉次公式。 -/
lemma moduleComposeApp_apply {K L : Complex A} {M N P : RightModule A D}
    (a : ∀ x : Dᵒᵖ, K ⟶ homComplex A (M.obj x) (N.obj x))
    (b : ∀ x : Dᵒᵖ, L ⟶ homComplex A (N.obj x) (P.obj x)) (x : Dᵒᵖ)
    (k l m : ℤ) (hm : k + l = m) (t : K.X k) (s : L.X l) :
    (moduleComposeApp A a b x).f m
      (ιTensorObj K L k l m hm (t ⊗ₜ[A] s)) =
    (k * l).negOnePow • (((a x).f k t).comp ((b x).f l s) hm) := by
  change (enrichedComposition _ _ _).f m
    ((a x ⊗ₘ b x).f m (ιTensorObj K L k l m hm (t ⊗ₜ[A] s))) = _
  rw [tensorMap_apply, enrichedComposition_apply]

/-- 全次数自然な変換族の合成も全次数自然。 -/
lemma moduleComposeApp_naturality {K L : Complex A} {M N P : RightModule A D}
    (a : ∀ x : Dᵒᵖ, K ⟶ homComplex A (M.obj x) (N.obj x))
    (b : ∀ x : Dᵒᵖ, L ⟶ homComplex A (N.obj x) (P.obj x))
    (ha : ∀ x y : Dᵒᵖ, (β_ K (x ⟶[Complex A] y)).hom ≫
      (M.map x y ⊗ₘ a y) ≫ enrichedComposition _ _ _ =
        (a x ⊗ₘ N.map x y) ≫ enrichedComposition _ _ _)
    (hb : ∀ x y : Dᵒᵖ, (β_ L (x ⟶[Complex A] y)).hom ≫
      (N.map x y ⊗ₘ b y) ≫ enrichedComposition _ _ _ =
        (b x ⊗ₘ P.map x y) ≫ enrichedComposition _ _ _) (x y : Dᵒᵖ) :
    (β_ (K ⊗ L) (x ⟶[Complex A] y)).hom ≫
      (M.map x y ⊗ₘ moduleComposeApp A a b y) ≫ enrichedComposition _ _ _ =
      (moduleComposeApp A a b x ⊗ₘ P.map x y) ≫ enrichedComposition _ _ _ := by
  apply triple_ext
  intro k l p m hm
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro t s f
  change (enrichedComposition _ _ _).f m
    ((M.map x y ⊗ₘ moduleComposeApp A a b y).f m
      ((signedSwap (K ⊗ L) (x ⟶[Complex A] y)).hom.f m
        (ιTensorObj (K ⊗ L) (x ⟶[Complex A] y) (k + l) p m hm
          (ιTensorObj K L k l (k + l) rfl (t ⊗ₜ[A] s) ⊗ₜ[A] f)))) =
    (enrichedComposition _ _ _).f m
      ((moduleComposeApp A a b x ⊗ₘ P.map x y).f m
        (ιTensorObj (K ⊗ L) (x ⟶[Complex A] y) (k + l) p m hm
          (ιTensorObj K L k l (k + l) rfl (t ⊗ₜ[A] s) ⊗ₜ[A] f)))
  rw [signedSwap_apply]
  simp only [Units.smul_def, map_zsmul]
  change ((k + l) * p).negOnePow • (enrichedComposition _ _ _).f m
    ((M.map x y ⊗ₘ moduleComposeApp A a b y).f m
      (ιTensorObj (x ⟶[Complex A] y) (K ⊗ L) p (k + l) m (by omega)
        (f ⊗ₜ[A] ιTensorObj K L k l (k + l) rfl (t ⊗ₜ[A] s)))) = _
  rw [tensorMap_apply, tensorMap_apply, enrichedComposition_apply,
    enrichedComposition_apply, mul_comm p (k + l), smul_smul,
    Int.units_mul_self, one_smul]
  apply Cochain.ext
  intro r n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  rw [Cochain.units_smul_v,
    Cochain.comp_v _ _ (by omega) r (r + p) n rfl (by omega),
    Cochain.comp_v _ _ hm r (r + (k + l)) n rfl (by omega),
    moduleComposeApp_apply, moduleComposeApp_apply,
    Cochain.units_smul_v, Cochain.units_smul_v,
    Cochain.comp_v _ _ rfl (r + p) (r + p + k) n rfl (by omega),
    Cochain.comp_v _ _ rfl r (r + k) (r + (k + l)) rfl (by omega)]
  change (k * l).negOnePow •
    (((b y).f l s).v (r + p + k) n (by omega)
      (((a y).f k t).v (r + p) (r + p + k) rfl (moduleAction A M f v rfl))) =
    ((k + l) * p).negOnePow • moduleAction A P f
      ((k * l).negOnePow • (((b x).f l s).v (r + k) (r + (k + l)) (by omega)
        (((a x).f k t).v r (r + k) rfl v))) (by omega)
  have h₁ := moduleParamNaturality_apply_of_sum A a ha
    (x := x) (y := y) (m := k + p) (n := r + p + k) (s := r + p) (l := r + k)
    t f v rfl (by omega) rfl rfl
  have h₂ := moduleParamNaturality_apply_of_sum A b hb
    (x := x) (y := y) (m := l + p) (n := n) (s := r + p + k) (l := r + (k + l))
    s f (((a x).f k t).v r (r + k) rfl v) rfl (by omega) (by omega) (by omega)
  rw [h₁]
  simp only [Units.smul_def, map_zsmul]
  rw [h₂]
  unfold moduleAction
  simp only [Units.smul_def, map_zsmul, smul_smul]
  change ((k * l).negOnePow * ((k * p).negOnePow * (l * p).negOnePow)) • (_ : (P.obj y).X n) =
    (((k + l) * p).negOnePow * (k * l).negOnePow) • (_ : (P.obj y).X n)
  simp only [← Int.negOnePow_add]
  congr 1
  congr 1
  ring
/-- パラメータ付き自然変換を tensor パラメータで合成する。 -/
def moduleParamCompose {K L : Complex A} {M N P : RightModule A D}
    (a : ModuleParamTrans A D K M N) (b : ModuleParamTrans A D L N P) :
    ModuleParamTrans A D (K ⊗ L) M P where
  app := moduleComposeApp A a.app b.app
  naturality := moduleComposeApp_naturality A a.app b.app a.naturality b.naturality

/-- 各対象の閉単位は全次数自然。 -/
lemma moduleIdentity_naturality (M : RightModule A D) (x y : Dᵒᵖ) :
    (β_ (𝟙_ (Complex A)) (x ⟶[Complex A] y)).hom ≫
      (M.map x y ⊗ₘ identity (M.obj y)) ≫ enrichedComposition _ _ _ =
    (identity (M.obj x) ⊗ₘ M.map x y) ≫ enrichedComposition _ _ _ := by
  rw [braiding_tensorUnit_left]
  rw [tensorHom_def, Category.assoc, Category.assoc,
    ← rightUnitor_inv_naturality_assoc, comp_identity, Category.comp_id]
  rw [tensorHom_def', Category.assoc, ← leftUnitor_naturality]
  have hi := identity_comp (M.obj x) (M.obj y)
  have hi' := congrArg (fun f => (λ_ (homComplex A (M.obj x) (M.obj y))).hom ≫ f) hi
  simp only [Iso.hom_inv_id_assoc, Category.comp_id] at hi'
  rw [← hi']

/-- 単位複体パラメータを持つ恒等自然変換。 -/
def moduleParamIdentity (M : RightModule A D) :
    ModuleParamTrans A D (𝟙_ (Complex A)) M M where
  app x := identity (M.obj x)
  naturality := moduleIdentity_naturality A M

variable (D) [Small.{u} D]
/-- Hom end の閉単位。 -/
def moduleIdentity (M : RightModule A D) : 𝟙_ (Complex A) ⟶ moduleHom A D M M :=
  (moduleHomEquiv A D _ M M).symm (moduleParamIdentity A M)

/-- Hom end の豊穣合成。 -/
def moduleComposition (M N P : RightModule A D) :
    moduleHom A D M N ⊗ moduleHom A D N P ⟶ moduleHom A D M P :=
  (moduleHomEquiv A D _ M P).symm
    { app x := moduleComposeApp A
        (fun y => moduleHomπ A D M N y.unop) (fun y => moduleHomπ A D N P y.unop) x
      naturality := moduleComposeApp_naturality A _ _
        (moduleHomπ_naturality A D M N) (moduleHomπ_naturality A D N P) }

/-- 単位の成分は各対象の恒等射。 -/
@[reassoc (attr := simp)]
lemma moduleIdentity_π (M : RightModule A D) (x : D) :
    moduleIdentity A D M ≫ moduleHomπ A D M M x = identity (M.obj (op x)) :=
  moduleHomEquiv_symm_π A D _ _ _ _ _

/-- end 合成の成分は各対象の豊穣合成。 -/
@[reassoc (attr := simp)]
lemma moduleComposition_π (M N P : RightModule A D) (x : D) :
    moduleComposition A D M N P ≫ moduleHomπ A D M P x =
    (moduleHomπ A D M N x ⊗ₘ moduleHomπ A D N P x) ≫ enrichedComposition _ _ _ :=
  moduleHomEquiv_symm_π A D _ _ _ _ _
end SerrePositivity.DifferentialGraded
end

end Composition

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "4.6.3.2" (partial := component) "仮定：可換基礎環上の小さい dg 圏 D（Lean が強い：通常の dg 加群の対象に限る）。結論：D 上の左 dg 加群と Dᵒᵖ 上の右 dg 加群を互いに逆な変換で対応させる（この仮定での HA の結論の一部に一致）。BM の部分オペラッドと全加群単体集合の同型は含まれない。"] _root_.SerrePositivity.DifferentialGraded.LeftModule.toRightOpposite
attribute [cite HA "4.6.3.2" (partial := component) "仮定：可換基礎環上の小さい dg 圏 D（Lean が強い：通常の dg 加群の対象に限る）。結論：D 上の左 dg 加群と Dᵒᵖ 上の右 dg 加群を互いに逆な変換で対応させる（この仮定での HA の結論の一部に一致）。BM の部分オペラッドと全加群単体集合の同型は含まれない。"] _root_.SerrePositivity.DifferentialGraded.leftModuleEquivRightOpposite
