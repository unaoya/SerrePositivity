module

public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations
public import SerrePositivity.DifferentialGraded.Module.ConeRotation
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
public import SerrePositivity.DifferentialGraded.Module.Basic
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import SerrePositivity.DifferentialGraded.Module.Disk
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Module.MaurerCartanTriangulated

## 概要
14 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## MaurerCartanEvaluation（旧 SerrePositivity/DifferentialGraded/Module/MaurerCartanEvaluation.lean） -/

/-!
概要：右 dg 加群の Maurer–Cartan 要素を各評価複体と全次数の作用へ送る。
方針：主 Hom の合成・微分の成分式と、次数一要素の符号付き自然性を使う。
規約：係数圏だけの Small 仮定で、全加群圏の Small は要求しない。
使われ方：coherent 図式の bar 微分を加えた実 dg 加群。
-/

@[expose] public section MaurerCartanEvaluation
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

variable (M : RightModule R D) (θ : (moduleHom R D M M).X 1)
  (hθ : (moduleHom R D M M).d 1 2 θ +
    compose R (x := M) (y := M) (z := M) θ θ (show (1 : ℤ) + 1 = 2 from rfl) = 0)

include hθ in
lemma moduleMaurerCartan_evaluation (x : D) :
    δ 1 2 ((moduleHomπ R D M M x).f 1 θ) +
      ((moduleHomπ R D M M x).f 1 θ).comp
        ((moduleHomπ R D M M x).f 1 θ) (show (1 : ℤ) + 1 = 2 from rfl) = 0 := by
  have h := congrArg ((moduleHomπ R D M M x).f 2) hθ
  simpa only [map_add, map_zero, differential, moduleHomElement_d_π,
    moduleHomCompose_π] using h

lemma moduleMaurerCartan_action (x y : Dᵒᵖ) (p : ℤ) (a : GradedHom R x y p) :
    ((M.map x y).f p a).comp ((moduleHomπ R D M M y.unop).f 1 θ) rfl +
      (p + 1).negOnePow • (((moduleHomπ R D M M x.unop).f 1 θ).comp
        ((M.map x y).f p a) (by omega : 1 + p = p + 1)) = 0 := by
  apply Cochain.ext
  intro i j hij
  have h := congrArg (fun c : Cochain (M.obj x) (M.obj y) (1 + p) =>
    c.v i j (by omega)) (moduleHomElement_naturality R D 1 θ x y p a)
  have hs : (p + 1).negOnePow = -p.negOnePow := by
    rw [Int.negOnePow_add]
    simp
  simp only [one_mul, Cochain.units_smul_v] at h
  rw [Cochain.comp_v _ _ _ i (i + p) j rfl (by omega),
    Cochain.comp_v _ _ _ i (i + 1) j rfl (by omega)] at h
  rw [Cochain.add_v, Cochain.units_smul_v,
    Cochain.comp_v _ _ _ i (i + p) j rfl (by omega),
    Cochain.comp_v _ _ _ i (i + 1) j rfl (by omega), hs]
  simpa only [Units.smul_def, Units.val_neg, neg_zsmul, ← sub_eq_add_neg, Cochain.zero_v] using
    sub_eq_zero.mpr h

end SerrePositivity.DifferentialGraded
end

end MaurerCartanEvaluation

/-! ## MaurerCartan（旧 SerrePositivity/DifferentialGraded/Module/MaurerCartan.lean） -/

/-!
概要：主 Hom の Maurer–Cartan 要素で右 dg 加群の微分を変更する。
方針：各評価の MC 複体と、同じ全次数 cochain を持つ作用鎖写像を組み合わせる。
規約：追加微分の閉性と二乗零を個別に要求せず、元の dg 作用を保持する。
使われ方：高次 coherent 図式の bar 余極限を実 dg 加群として構成する。
-/

@[expose] public section MaurerCartan
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (M : RightModule R D) (θ : (moduleHom R D M M).X 1)
  (hθ : (moduleHom R D M M).d 1 2 θ +
    compose R (x := M) (y := M) (z := M) θ θ (show (1 : ℤ) + 1 = 2 from rfl) = 0)

abbrev moduleMaurerCartanValue (x : Dᵒᵖ) : Complex R :=
  maurerCartanPerturbComplex (M.obj x) ((moduleHomπ R D M M x.unop).f 1 θ)
    (moduleMaurerCartan_evaluation R D M θ hθ x.unop)

def moduleMaurerCartanMap (x y : Dᵒᵖ) :
    (x ⟶[Complex R] y) ⟶ homComplex R (moduleMaurerCartanValue R D M θ hθ x)
      (moduleMaurerCartanValue R D M θ hθ y) :=
  maurerCartanPerturbHomMap _ _
    (moduleMaurerCartan_evaluation R D M θ hθ x.unop)
    (moduleMaurerCartan_evaluation R D M θ hθ y.unop)
    _ (M.map x y) (moduleMaurerCartan_action R D M θ x y)

@[simp] lemma moduleMaurerCartanMap_v (x y : Dᵒᵖ) (p : ℤ)
    (a : GradedHom R x y p) (i j : ℤ) (hij : i + p = j) :
    ((moduleMaurerCartanMap R D M θ hθ x y).f p a).v i j hij =
      ((M.map x y).f p a).v i j hij := rfl

/-- 全次数作用を保持した実右 dg 加群。 -/
def moduleMaurerCartan : RightModule R D where
  obj := moduleMaurerCartanValue R D M θ hθ
  map := moduleMaurerCartanMap R D M θ hθ
  map_id x := by
    apply (unitCycleEquiv _).injective
    apply Subtype.ext
    change (cycleFromUnit _ (eId (Complex R) x ≫
      moduleMaurerCartanMap R D M θ hθ x x)).val =
        (cycleFromUnit _ (identity (moduleMaurerCartanValue R D M θ hθ x))).val
    rw [cycleFromUnit_postcomp]
    change (moduleMaurerCartanMap R D M θ hθ x x).f 0 (unitElement R x).val =
      (cycleFromUnit _ (identity (moduleMaurerCartanValue R D M θ hθ x))).val
    simp only [identity, cycleFromUnit_unitFromCycle]
    apply Cochain.ext
    intro i j hij
    rw [moduleMaurerCartanMap_v, moduleMap_unit_cochain]
    rfl
  map_comp x y z := by
    apply tensorHom_ext
    intro p q n hn
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro f g
    change (moduleMaurerCartanMap R D M θ hθ x z).f n (forward R f g hn) =
      (enrichedComposition _ _ _).f n
        ((moduleMaurerCartanMap R D M θ hθ x y ⊗ₘ
          moduleMaurerCartanMap R D M θ hθ y z).f n
            (ιTensorObj (x ⟶[Complex R] y) (y ⟶[Complex R] z)
              p q n hn (f ⊗ₜ[R] g)))
    rw [tensorMap_apply, enrichedComposition_apply]
    apply Cochain.ext
    intro i j hij
    rw [moduleMaurerCartanMap_v, moduleMap_forward]
    simp only [Cochain.units_smul_v]
    rw [Cochain.comp_v _ _ hn i (i + p) j rfl (by omega)]
    rw [Cochain.comp_v _ _ hn i (i + p) j rfl (by omega)]
    simp only [moduleMaurerCartanMap_v]

end SerrePositivity.DifferentialGraded
end

end MaurerCartan

/-! ## MaurerCartanTargetHom（旧 SerrePositivity/DifferentialGraded/Module/MaurerCartanTargetHom.lean） -/

/-!
概要：標的だけを MC 変形した加群 Hom の全次数係数を、元の Hom と比較する。
方針：各評価の標的だけの cochain 移送を、主 Hom end の全次数自然性で再構成する。
規約：始域加群を固定し、係数 dg 圏だけの Small 仮定を使う。
使われ方：MC 摂動後の bar の終端 HA 成分と元の成分の比較。
-/

@[expose] public section MaurerCartanTargetHom
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (N : RightModule R D) (ψ : (moduleHom R D N N).X 1)
  (hψ : (moduleHom R D N N).d 1 2 ψ +
    compose R (x := N) (y := N) (z := N) ψ ψ (show (1 : ℤ) + 1 = 2 from rfl) = 0)


lemma moduleMaurerCartan_map_v (x y : Dᵒᵖ) (p : ℤ)
    (a : GradedHom R x y p) (i j : ℤ) (hij : i + p = j) :
    (((moduleMaurerCartan R D N ψ hψ).map x y).f p a).v i j hij =
      ((N.map x y).f p a).v i j hij := rfl

def moduleMaurerCartanTargetRebase (M : RightModule R D) (q : ℤ)
    (z : (moduleHom R D M N).X q) :
    (moduleHom R D M (moduleMaurerCartan R D N ψ hψ)).X q :=
  moduleHomElementMk R D q
    (fun x => maurerCartanTargetRebaseCochain ((moduleHomπ R D N N x.unop).f 1 ψ)
      (moduleMaurerCartan_evaluation R D N ψ hψ x.unop) ((moduleHomπ R D M N x.unop).f q z)) (by
    intro x y p a
    apply Cochain.ext
    intro i j hij
    have h := congrArg (fun f => f.v i j hij) (moduleHomElement_naturality R D q z x y p a)
    rw [Cochain.units_smul_v] at h ⊢
    rw [Cochain.comp_v _ _ _ i (i + p) j rfl (by omega),
      Cochain.comp_v _ _ _ i (i + q) j rfl (by omega)] at h ⊢
    simpa only [maurerCartanTargetRebaseCochain, Cochain.mk_v, moduleMaurerCartan_map_v] using h)

def moduleMaurerCartanTargetForget (M : RightModule R D) (q : ℤ)
    (z : (moduleHom R D M (moduleMaurerCartan R D N ψ hψ)).X q) :
    (moduleHom R D M N).X q :=
  moduleHomElementMk R D q
    (fun x => maurerCartanTargetForgetCochain ((moduleHomπ R D N N x.unop).f 1 ψ)
      (moduleMaurerCartan_evaluation R D N ψ hψ x.unop)
      ((moduleHomπ R D M (moduleMaurerCartan R D N ψ hψ) x.unop).f q z)) (by
    intro x y p a
    apply Cochain.ext
    intro i j hij
    have h := congrArg (fun f => f.v i j hij) (moduleHomElement_naturality R D q z x y p a)
    rw [Cochain.units_smul_v] at h ⊢
    rw [Cochain.comp_v _ _ _ i (i + p) j rfl (by omega),
      Cochain.comp_v _ _ _ i (i + q) j rfl (by omega)] at h ⊢
    simpa only [maurerCartanTargetForgetCochain, Cochain.mk_v, moduleMaurerCartan_map_v] using h)

lemma moduleMaurerCartanTargetRebase_π (M : RightModule R D) (q : ℤ)
    (z : (moduleHom R D M N).X q) (x : D) :
    (moduleHomπ R D M (moduleMaurerCartan R D N ψ hψ) x).f q
      (moduleMaurerCartanTargetRebase R D N ψ hψ M q z) =
    maurerCartanTargetRebaseCochain ((moduleHomπ R D N N x).f 1 ψ)
      (moduleMaurerCartan_evaluation R D N ψ hψ x) ((moduleHomπ R D M N x).f q z) :=
  moduleHomElementMk_π R D q _ _ x

lemma moduleMaurerCartanTargetForget_π (M : RightModule R D) (q : ℤ)
    (z : (moduleHom R D M (moduleMaurerCartan R D N ψ hψ)).X q) (x : D) :
    (moduleHomπ R D M N x).f q (moduleMaurerCartanTargetForget R D N ψ hψ M q z) =
    maurerCartanTargetForgetCochain ((moduleHomπ R D N N x).f 1 ψ)
      (moduleMaurerCartan_evaluation R D N ψ hψ x)
      ((moduleHomπ R D M (moduleMaurerCartan R D N ψ hψ) x).f q z) :=
  moduleHomElementMk_π R D q _ _ x

lemma moduleMaurerCartanTargetForget_rebase (M : RightModule R D) (q : ℤ)
    (z : (moduleHom R D M N).X q) :
    moduleMaurerCartanTargetForget R D N ψ hψ M q
      (moduleMaurerCartanTargetRebase R D N ψ hψ M q z) = z := by
  apply moduleHomElement_ext R D
  intro x
  rw [moduleMaurerCartanTargetForget_π, moduleMaurerCartanTargetRebase_π]
  apply Cochain.ext
  intro i j hij
  rfl

lemma moduleMaurerCartanTargetRebase_forget (M : RightModule R D) (q : ℤ)
    (z : (moduleHom R D M (moduleMaurerCartan R D N ψ hψ)).X q) :
    moduleMaurerCartanTargetRebase R D N ψ hψ M q
      (moduleMaurerCartanTargetForget R D N ψ hψ M q z) = z := by
  apply moduleHomElement_ext R D
  intro x
  rw [moduleMaurerCartanTargetRebase_π, moduleMaurerCartanTargetForget_π]
  apply Cochain.ext
  intro i j hij
  rfl


def moduleMaurerCartanTargetHomEquiv (M : RightModule R D) (q : ℤ) :
    (moduleHom R D M N).X q ≃ₗ[R]
      (moduleHom R D M (moduleMaurerCartan R D N ψ hψ)).X q where
  toFun := moduleMaurerCartanTargetRebase R D N ψ hψ M q
  invFun := moduleMaurerCartanTargetForget R D N ψ hψ M q
  left_inv := moduleMaurerCartanTargetForget_rebase R D N ψ hψ M q
  right_inv := moduleMaurerCartanTargetRebase_forget R D N ψ hψ M q
  map_add' z w := by
    apply moduleHomElement_ext R D
    intro x
    simp only [map_add, moduleMaurerCartanTargetRebase_π]
    apply Cochain.ext
    intro i j hij
    rfl
  map_smul' c z := by
    apply moduleHomElement_ext R D
    intro x
    simp only [map_smul, moduleMaurerCartanTargetRebase_π, RingHom.id_apply]
    apply Cochain.ext
    intro i j hij
    rfl

end SerrePositivity.DifferentialGraded
end

end MaurerCartanTargetHom

/-! ## MaurerCartanTargetHomDifferential（旧 SerrePositivity/DifferentialGraded/Module/MaurerCartanTargetHomDifferential.lean） -/

/-!
概要：標的だけの MC 変形に対する加群 Hom の微分と、元の始域からの斉次合成を比較する。
方針：各評価の標的変形の微分式を主 Hom end へ戻す。
規約：元の全次数 Hom を使い、閉性を仮定する版は別名で供給する。
使われ方：bar の末端 HA 方程式を実 MC 摂動後の方程式へ移す。
-/

@[expose] public section MaurerCartanTargetHomDifferential
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (N : RightModule R D) (ψ : (moduleHom R D N N).X 1)
  (hψ : (moduleHom R D N N).d 1 2 ψ +
    compose R (x := N) (y := N) (z := N) ψ ψ (show (1 : ℤ) + 1 = 2 from rfl) = 0)

def moduleMaurerCartanTargetDifferential (M : RightModule R D) (q : ℤ)
    (z : (moduleHom R D M N).X q) : (moduleHom R D M N).X (q + 1) :=
  let A : (moduleHom R D M N).X (q + 1) := (moduleHom R D M N).d q (q + 1) z
  let B : (moduleHom R D M N).X (q + 1) := compose R (x := M) (y := N) (z := N) ψ z rfl
  A + B

lemma moduleMaurerCartanTargetForget_d_rebase (M : RightModule R D) (q : ℤ)
    (z : (moduleHom R D M N).X q) :
    moduleMaurerCartanTargetForget R D N ψ hψ M (q + 1)
      ((moduleHom R D M (moduleMaurerCartan R D N ψ hψ)).d q (q + 1)
        (moduleMaurerCartanTargetRebase R D N ψ hψ M q z)) =
      moduleMaurerCartanTargetDifferential R D N ψ M q z := by
  apply moduleHomElement_ext R D
  intro x
  rw [moduleMaurerCartanTargetForget_π, moduleHomElement_d_π,
    moduleMaurerCartanTargetRebase_π]
  unfold moduleMaurerCartanTargetDifferential
  rw [map_add, moduleHomElement_d_π, moduleHomCompose_π]
  exact maurerCartanTargetHom_δ ((moduleHomπ R D N N x).f 1 ψ)
    (moduleMaurerCartan_evaluation R D N ψ hψ x) q ((moduleHomπ R D M N x).f q z)

lemma moduleMaurerCartanTargetRebase_d (M : RightModule R D) (q : ℤ)
    (z : (moduleHom R D M N).X q) :
    (moduleHom R D M (moduleMaurerCartan R D N ψ hψ)).d q (q + 1)
      (moduleMaurerCartanTargetRebase R D N ψ hψ M q z) =
    moduleMaurerCartanTargetRebase R D N ψ hψ M (q + 1)
      (moduleMaurerCartanTargetDifferential R D N ψ M q z) := by
  have h := congrArg (moduleMaurerCartanTargetRebase R D N ψ hψ M (q + 1))
    (moduleMaurerCartanTargetForget_d_rebase R D N ψ hψ M q z)
  simpa only [moduleMaurerCartanTargetRebase_forget] using h

lemma moduleMaurerCartanTargetRebase_d_of_closed (M : RightModule R D) (q : ℤ)
    (z : (moduleHom R D M N).X q) (hz : (moduleHom R D M N).d q (q + 1) z = 0) :
    (moduleHom R D M (moduleMaurerCartan R D N ψ hψ)).d q (q + 1)
      (moduleMaurerCartanTargetRebase R D N ψ hψ M q z) =
    moduleMaurerCartanTargetRebase R D N ψ hψ M (q + 1)
      (compose R (x := M) (y := N) (z := N) ψ z rfl) := by
  rw [moduleMaurerCartanTargetRebase_d, moduleMaurerCartanTargetDifferential, hz, zero_add]

lemma moduleMaurerCartanTargetRebase_comp (L M : RightModule R D) {p q n : ℤ}
    (f : (moduleHom R D L M).X p) (g : (moduleHom R D M N).X q) (hn : p + q = n) :
    moduleMaurerCartanTargetRebase R D N ψ hψ L n
      (compose R (x := L) (y := M) (z := N) g f hn) =
    compose R (x := L) (y := M) (z := moduleMaurerCartan R D N ψ hψ)
      (moduleMaurerCartanTargetRebase R D N ψ hψ M q g) f hn := by
  apply moduleHomElement_ext R D
  intro x
  rw [moduleMaurerCartanTargetRebase_π, moduleHomCompose_π,
    moduleHomCompose_π, moduleMaurerCartanTargetRebase_π]
  apply Cochain.ext
  intro i j hij
  simp only [maurerCartanTargetRebaseCochain, Cochain.mk_v]
  rw [Cochain.comp_v _ _ hn i (i + p) j rfl (by omega),
    Cochain.comp_v _ _ hn i (i + p) j rfl (by omega)]
  rfl

end SerrePositivity.DifferentialGraded
end

end MaurerCartanTargetHomDifferential

/-! ## ContractibleTriangleIso（旧 SerrePositivity/DifferentialGraded/Module/ContractibleTriangleIso.lean） -/

/-! # 自明三角形と恒等cone三角形の同型 -/

@[expose] public section ContractibleTriangleIso
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated Limits ZeroObject
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 第三対象の収縮を使い、恒等cone三角形を自明三角形と比較する。 -/
def moduleHomotopyIdentityConeTriangleIso (M : ModuleCategory A D) :
    contractibleTriangle ((moduleToHomotopy A D).obj M) ≅
      moduleHomotopyConeTriangle A D (𝟙 M) := by
  let Q := moduleToHomotopy A D
  let T := moduleHomotopyConeTriangle A D (𝟙 M)
  let h := moduleConeId_isZero A D M
  let e : (0 : ModuleHomotopyCategory A D) ≅ Q.obj (moduleCone A D (𝟙 M)) := h.isoZero.symm
  refine Triangle.isoMk (contractibleTriangle (Q.obj M)) T
    (Iso.refl (Q.obj M)) (Iso.refl (Q.obj M)) e ?_ ?_ ?_
  · change (𝟙 (Q.obj M)) ≫ 𝟙 _ = 𝟙 _ ≫ Q.map (𝟙 M)
    rw [Q.map_id, Category.id_comp]
  · exact h.eq_of_tgt _ _
  · exact (isZero_zero (ModuleHomotopyCategory A D)).eq_of_src _ _

end SerrePositivity.DifferentialGraded
end

end ContractibleTriangleIso

/-! ## DistinguishedTriangles（旧 SerrePositivity/DifferentialGraded/Module/DistinguishedTriangles.lean） -/

/-! # K(D)の標準coneによるdistinguished三角形のクラス

回転と八面体の証明前にはPretriangulated/Triangulatedのインスタンスを置かない。
-/

@[expose] public section DistinguishedTriangles
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleDistinguishedTriangles : Set (Triangle (ModuleHomotopyCategory A D)) :=
  {T | ∃ (M N : ModuleCategory A D) (f : M ⟶ N),
    Nonempty (T ≅ moduleHomotopyConeTriangle A D f)}

lemma moduleHomotopyConeTriangle_distinguished {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleHomotopyConeTriangle A D f ∈ moduleDistinguishedTriangles A D :=
  ⟨M, N, f, ⟨Iso.refl _⟩⟩

lemma moduleDistinguished_isomorphic (T₁ : Triangle (ModuleHomotopyCategory A D))
    (hT₁ : T₁ ∈ moduleDistinguishedTriangles A D)
    (T₂ : Triangle (ModuleHomotopyCategory A D)) (e : T₂ ≅ T₁) :
    T₂ ∈ moduleDistinguishedTriangles A D := by
  obtain ⟨M, N, f, ⟨e'⟩⟩ := hT₁
  exact ⟨M, N, f, ⟨e ≪≫ e'⟩⟩

lemma moduleDistinguished_cocone {M N : ModuleHomotopyCategory A D} (f : M ⟶ N) :
    ∃ (T : ModuleHomotopyCategory A D) (g : N ⟶ T) (h : T ⟶ M⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ moduleDistinguishedTriangles A D := by
  obtain ⟨M⟩ := M
  obtain ⟨N⟩ := N
  obtain ⟨f, rfl⟩ := (moduleToHomotopy A D).map_surjective f
  exact ⟨_, _, _, moduleHomotopyConeTriangle_distinguished A D f⟩

lemma moduleDistinguished_contractible (M : ModuleHomotopyCategory A D) :
    contractibleTriangle M ∈ moduleDistinguishedTriangles A D := by
  obtain ⟨M⟩ := M
  refine ⟨M, M, 𝟙 M, ⟨?_⟩⟩
  exact moduleHomotopyIdentityConeTriangleIso A D M

lemma moduleDistinguished_complete (T₁ T₂ : Triangle (ModuleHomotopyCategory A D))
    (hT₁ : T₁ ∈ moduleDistinguishedTriangles A D) (hT₂ : T₂ ∈ moduleDistinguishedTriangles A D)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂)
    (fac : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c : T₁.obj₃ ⟶ T₂.obj₃,
      T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧ T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃ := by
  obtain ⟨M, N, f, ⟨e₁⟩⟩ := hT₁
  obtain ⟨M', N', g, ⟨e₂⟩⟩ := hT₂
  let a' := e₁.inv.hom₁ ≫ a ≫ e₂.hom.hom₁
  let b' := e₁.inv.hom₂ ≫ b ≫ e₂.hom.hom₂
  have hf : (moduleToHomotopy A D).map f ≫ b' = a' ≫ (moduleToHomotopy A D).map g := by
    dsimp [a', b']
    have h₁ := e₁.inv.comm₁
    have h₂ := e₂.hom.comm₁
    change (moduleToHomotopy A D).map f ≫ e₁.inv.hom₂ = e₁.inv.hom₁ ≫ T₁.mor₁ at h₁
    change T₂.mor₁ ≫ e₂.hom.hom₂ = e₂.hom.hom₁ ≫ (moduleToHomotopy A D).map g at h₂
    simp only [reassoc_of% h₁, reassoc_of% fac, h₂, Category.assoc]
  obtain ⟨t, ht₁, ht₂⟩ := moduleHomotopyConeTriangle_complete A D f g a' b' hf
  let γ := e₁.hom ≫ t ≫ e₂.inv
  have hγ₁ : γ.hom₁ = a := by
    change e₁.hom.hom₁ ≫ t.hom₁ ≫ e₂.inv.hom₁ = a
    rw [ht₁]
    dsimp only [a']
    simp only [Category.assoc, Iso.hom_inv_id_triangle_hom₁_assoc,
      Iso.hom_inv_id_triangle_hom₁, Category.comp_id]
  have hγ₂ : γ.hom₂ = b := by
    change e₁.hom.hom₂ ≫ t.hom₂ ≫ e₂.inv.hom₂ = b
    rw [ht₂]
    dsimp only [b']
    simp only [Category.assoc, Iso.hom_inv_id_triangle_hom₂_assoc,
      Iso.hom_inv_id_triangle_hom₂, Category.comp_id]
  refine ⟨γ.hom₃, ?_, ?_⟩
  · simpa only [hγ₂] using γ.comm₂
  · simpa only [hγ₁] using γ.comm₃


@[reassoc] lemma moduleDistinguished_comp_zero₁₂
    (T : Triangle (ModuleHomotopyCategory A D)) (hT : T ∈ moduleDistinguishedTriangles A D) :
    T.mor₁ ≫ T.mor₂ = 0 := by
  obtain ⟨c, hc, _⟩ := moduleDistinguished_complete A D
    (contractibleTriangle T.obj₁) T (moduleDistinguished_contractible A D T.obj₁) hT
    (𝟙 T.obj₁) T.mor₁ rfl
  simpa only [contractibleTriangle_mor₂, zero_comp] using hc.symm

end SerrePositivity.DifferentialGraded
end

end DistinguishedTriangles

/-! ## ConeShiftTriangle（旧 SerrePositivity/DifferentialGraded/Module/ConeShiftTriangle.lean） -/

/-! # K(D)の標準cone三角形の整数shift比較 -/

@[expose] public section ConeShiftTriangle
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 商関手のshift比較を含む標準cone三角形のshift同型。 -/
def moduleHomotopyConeShiftIso (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :=
  triangleShiftMapIso (moduleToHomotopy A D) s (moduleConeTriangle A D f)
    (moduleConeTriangle A D (moduleShiftMap A D s f)) (moduleConeTriangleShiftIso A D s f)

lemma moduleDistinguished_ofConeIso {M N : ModuleCategory A D} (f : M ⟶ N)
    (T : Triangle (ModuleHomotopyCategory A D))
    (e : T ≅ (moduleToHomotopy A D).mapTriangle.obj (moduleConeTriangle A D f)) :
    T ∈ moduleDistinguishedTriangles A D := ⟨M, N, f, ⟨e⟩⟩

set_option maxHeartbeats 800000 in
-- 豊穣coneと商shiftの型変換を含む、この証明のカーネル検査に上限を指定する。
lemma moduleDistinguished_shift (T : Triangle (ModuleHomotopyCategory A D))
    (hT : T ∈ moduleDistinguishedTriangles A D) (s : ℤ) :
    (Triangle.shiftFunctor (ModuleHomotopyCategory A D) s).obj T ∈
      moduleDistinguishedTriangles A D := by
  change ∃ (M N : ModuleCategory A D) (f : M ⟶ N),
    Nonempty (T ≅ (moduleToHomotopy A D).mapTriangle.obj (moduleConeTriangle A D f)) at hT
  obtain ⟨M, N, f, ⟨e⟩⟩ := hT
  let e' := triangleShiftIsoTrans s T
    ((moduleToHomotopy A D).mapTriangle.obj (moduleConeTriangle A D f))
    ((moduleToHomotopy A D).mapTriangle.obj (moduleConeTriangle A D (moduleShiftMap A D s f)))
    e (moduleHomotopyConeShiftIso A D s f)
  exact moduleDistinguished_ofConeIso A D (moduleShiftMap A D s f) _ e'
end SerrePositivity.DifferentialGraded
end

end ConeShiftTriangle

/-! ## ConeRotationTriangle（旧 SerrePositivity/DifferentialGraded/Module/ConeRotationTriangle.lean） -/

/-! # K(D)の標準cone三角形の回転同型 -/

@[expose] public section ConeRotationTriangle
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

@[reassoc] lemma moduleConeRotation_connecting_homotopy {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleToHomotopy A D).map (moduleConeConnecting A D f) ≫
      (moduleToHomotopy A D).map (moduleConeRotationHom A D f) =
        (moduleToHomotopy A D).map (moduleConeInr A D (moduleConeInr A D f)) := by
  rw [← CategoryTheory.Functor.map_comp]
  exact (moduleToHomotopy_map_eq_iff A D _ _).2 ⟨moduleConeRotationConnectingHomotopy A D f⟩

/-- 標準cone三角形の回転は、その右包含の標準cone三角形と同型。 -/
def moduleHomotopyConeRotationIso {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHomotopyConeTriangle A D f).rotate ≅
      moduleHomotopyConeTriangle A D (moduleConeInr A D f) := by
  let Q := moduleToHomotopy A D
  refine Triangle.isoMk ((moduleHomotopyConeTriangle A D f).rotate)
    (moduleHomotopyConeTriangle A D (moduleConeInr A D f))
    (Iso.refl (Q.obj N)) (Iso.refl (Q.obj (moduleCone A D f)))
    (moduleConeRotationShiftIso A D f) ?_ ?_ ?_
  · change Q.map (moduleConeInr A D f) ≫ 𝟙 _ = 𝟙 _ ≫ Q.map (moduleConeInr A D f)
    rw [Category.comp_id, Category.id_comp]
  · change (Q.map (moduleConeConnecting A D f) ≫ (Q.commShiftIso (1 : ℤ)).hom.app M) ≫
      ((Q.commShiftIso (1 : ℤ)).inv.app M ≫ Q.map (moduleConeRotationHom A D f)) =
        𝟙 _ ≫ Q.map (moduleConeInr A D (moduleConeInr A D f))
    rw [Category.assoc, Iso.hom_inv_id_app_assoc, Category.id_comp]
    exact moduleConeRotation_connecting_homotopy A D f
  · change (-(Q.map f)⟦(1 : ℤ)⟧') ≫ (𝟙 (Q.obj N))⟦(1 : ℤ)⟧' =
      ((Q.commShiftIso (1 : ℤ)).inv.app M ≫ Q.map (moduleConeRotationHom A D f)) ≫
        (Q.map (moduleConeConnecting A D (moduleConeInr A D f)) ≫
          (Q.commShiftIso (1 : ℤ)).hom.app N)
    rw [(shiftFunctor (ModuleHomotopyCategory A D) (1 : ℤ)).map_id, Category.comp_id]
    have hn := (Q.commShiftIso (1 : ℤ)).hom.naturality f
    change Q.map (f⟦(1 : ℤ)⟧') ≫ (Q.commShiftIso (1 : ℤ)).hom.app N =
      (Q.commShiftIso (1 : ℤ)).hom.app M ≫ (Q.map f)⟦(1 : ℤ)⟧' at hn
    symm
    calc
      _ = (Q.commShiftIso (1 : ℤ)).inv.app M ≫
          Q.map (moduleConeRotationHom A D f ≫
            moduleConeConnecting A D (moduleConeInr A D f)) ≫
              (Q.commShiftIso (1 : ℤ)).hom.app N := by
        simp only [Q.map_comp, Category.assoc]
      _ = (Q.commShiftIso (1 : ℤ)).inv.app M ≫ Q.map (-f⟦(1 : ℤ)⟧') ≫
          (Q.commShiftIso (1 : ℤ)).hom.app N := by rw [moduleConeRotation_connecting]
      _ = -((Q.commShiftIso (1 : ℤ)).inv.app M ≫
          (Q.map (f⟦(1 : ℤ)⟧') ≫ (Q.commShiftIso (1 : ℤ)).hom.app N)) := by
        rw [Q.map_neg, Preadditive.neg_comp, Preadditive.comp_neg]
      _ = -((Q.commShiftIso (1 : ℤ)).inv.app M ≫
          ((Q.commShiftIso (1 : ℤ)).hom.app M ≫ (Q.map f)⟦(1 : ℤ)⟧')) :=
        congrArg (fun a => -((Q.commShiftIso (1 : ℤ)).inv.app M ≫ a)) hn
      _ = -(Q.map f)⟦(1 : ℤ)⟧' := by rw [Iso.inv_hom_id_app_assoc]

lemma moduleDistinguished_rotate (T : Triangle (ModuleHomotopyCategory A D))
    (hT : T ∈ moduleDistinguishedTriangles A D) :
    T.rotate ∈ moduleDistinguishedTriangles A D := by
  obtain ⟨M, N, f, ⟨e⟩⟩ := hT
  exact ⟨N, moduleCone A D f, moduleConeInr A D f,
    ⟨(rotate _).mapIso e ≪≫ moduleHomotopyConeRotationIso A D f⟩⟩


@[reassoc] lemma moduleDistinguished_comp_zero₂₃
    (T : Triangle (ModuleHomotopyCategory A D)) (hT : T ∈ moduleDistinguishedTriangles A D) :
    T.mor₂ ≫ T.mor₃ = 0 := by
  have h := moduleDistinguished_comp_zero₁₂ A D T.rotate (moduleDistinguished_rotate A D T hT)
  exact h

@[reassoc] lemma moduleDistinguished_comp_zero₃₁
    (T : Triangle (ModuleHomotopyCategory A D)) (hT : T ∈ moduleDistinguishedTriangles A D) :
    T.mor₃ ≫ T.mor₁⟦(1 : ℤ)⟧' = 0 := by
  have h := moduleDistinguished_comp_zero₂₃ A D T.rotate (moduleDistinguished_rotate A D T hT)
  change T.mor₃ ≫ (-T.mor₁⟦(1 : ℤ)⟧') = 0 at h
  rw [Preadditive.comp_neg, neg_eq_zero] at h
  exact h

end SerrePositivity.DifferentialGraded
end

end ConeRotationTriangle

/-! ## ConeCompositionTriangle（旧 SerrePositivity/DifferentialGraded/Module/ConeCompositionTriangle.lean） -/

/-! # 合成cone三角形とそのdistinguished性 -/

@[expose] public section ConeCompositionTriangle
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
lemma triangle_comp_shift_id_of_eq {C : Type*} [Category* C] [HasShift C ℤ]
    {X Y Z : C} (a : X ⟶ Y⟦(1 : ℤ)⟧) (b : X ⟶ Z) (c : Z ⟶ Y⟦(1 : ℤ)⟧)
    (h : a = b ≫ c) : a ≫ (𝟙 Y)⟦(1 : ℤ)⟧' = b ≫ c := by
  rw [(shiftFunctor C (1 : ℤ)).map_id, Category.comp_id]
  exact h

lemma map_comp_shift_comm {C E : Type*} [Category* C] [Category* E]
    [HasShift C ℤ] [HasShift E ℤ] (F : C ⥤ E) [F.CommShift ℤ]
    {X Y Z : C} (f : X ⟶ Y⟦(1 : ℤ)⟧) (g : Y ⟶ Z) :
    F.map (f ≫ g⟦(1 : ℤ)⟧') ≫ (F.commShiftIso (1 : ℤ)).hom.app Z =
      (F.map f ≫ (F.commShiftIso (1 : ℤ)).hom.app Y) ≫ (F.map g)⟦(1 : ℤ)⟧' := by
  have hn := (F.commShiftIso (1 : ℤ)).hom.naturality g
  change F.map (g⟦(1 : ℤ)⟧') ≫ (F.commShiftIso (1 : ℤ)).hom.app Z =
    (F.commShiftIso (1 : ℤ)).hom.app Y ≫ (F.map g)⟦(1 : ℤ)⟧' at hn
  rw [F.map_comp, Category.assoc, hn, ← Category.assoc]

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleEvaluation_registeredShift (s : ℤ) {M N : ModuleCategory A D}
    (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).map (f⟦s⟧') = ((moduleEvaluation A D x).map f)⟦s⟧' :=
  moduleShiftFunctor_map_eval A D s f x

def moduleConeCompSecondMap {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    moduleCone A D (f ≫ g) ⟶ moduleCone A D g :=
  moduleConeMap A D (f ≫ g) g f (𝟙 P) (by simp)

lemma moduleConeCompSecondMap_eval {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P)
    (x : D) :
    (moduleEvaluation A D x).map (moduleConeCompSecondMap A D f g) =
      CochainComplex.mappingCone.map ((moduleEvaluation A D x).map (f ≫ g))
        ((moduleEvaluation A D x).map g) ((moduleEvaluation A D x).map f)
        (𝟙 ((moduleEvaluation A D x).obj P))
        (by rw [CategoryTheory.Functor.map_comp, Category.comp_id]) := by
  unfold moduleConeCompSecondMap
  simpa only [CategoryTheory.Functor.map_id] using
    moduleConeMap_eval A D (f ≫ g) g f (𝟙 P) (by simp) x

lemma moduleConeComp_inr_inv {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    moduleConeInr A D (moduleConeCompMap A D f g) ≫ moduleConeCompInv A D f g =
      moduleConeCompSecondMap A D f g := by
  apply moduleMorphism_ext
  intro x
  rw [(moduleEvaluation A D x).map_comp, moduleConeInr_eval, moduleConeCompInv_eval]
  exact (complexConeComp_inr_inv ((moduleEvaluation A D x).map f)
    ((moduleEvaluation A D x).map g) ((moduleEvaluation A D x).map (f ≫ g))
    ((moduleEvaluation A D x).map_comp f g)
    ((moduleEvaluation A D x).map (moduleConeCompMap A D f g))
    (moduleConeCompMap_eval A D f g x)).trans (moduleConeCompSecondMap_eval A D f g x).symm

lemma moduleConeComp_hom_connecting {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    moduleConeCompHom A D f g ≫ moduleConeConnecting A D (moduleConeCompMap A D f g) =
      moduleConeConnecting A D g ≫ (moduleConeInr A D f)⟦(1 : ℤ)⟧' := by
  apply moduleMorphism_ext
  intro x
  rw [(moduleEvaluation A D x).map_comp (moduleConeCompHom A D f g)
      (moduleConeConnecting A D (moduleConeCompMap A D f g)),
    moduleConeCompHom_eval, moduleConeConnecting_eval]
  conv_rhs => rw [(moduleEvaluation A D x).map_comp]
  rw [moduleConeConnecting_eval A D g x,
    moduleEvaluation_registeredShift A D 1 (moduleConeInr A D f) x, moduleConeInr_eval A D f x]
  exact complexConeComp_hom_connecting _ _ _ _ _ _

/-- cone(f)→cone(f≫g)→cone(g)→cone(f)[1]。 -/
def moduleConeCompTriangle {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    Triangle (ModuleCategory A D) :=
  Triangle.mk (moduleConeCompMap A D f g) (moduleConeCompSecondMap A D f g)
    (moduleConeConnecting A D g ≫ (moduleConeInr A D f)⟦(1 : ℤ)⟧')

abbrev moduleHomotopyConeCompTriangle {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    Triangle (ModuleHomotopyCategory A D) :=
  (moduleToHomotopy A D).mapTriangle.obj (moduleConeCompTriangle A D f g)

/-- 合成cone三角形の第三射について、商関手のshift比較を含む自然性の等式。 -/
lemma moduleHomotopyConeComp_mor₃ {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    (moduleToHomotopy A D).map (moduleConeConnecting A D g ≫ (moduleConeInr A D f)⟦(1 : ℤ)⟧') ≫
      ((moduleToHomotopy A D).commShiftIso (1 : ℤ)).hom.app (moduleCone A D f) =
        ((moduleToHomotopy A D).map (moduleConeConnecting A D g) ≫
          ((moduleToHomotopy A D).commShiftIso (1 : ℤ)).hom.app N) ≫
          ((moduleToHomotopy A D).map (moduleConeInr A D f))⟦(1 : ℤ)⟧' :=
  map_comp_shift_comm (moduleToHomotopy A D)
    (X := moduleCone A D g) (Y := N) (Z := moduleCone A D f)
    (moduleConeConnecting A D g) (moduleConeInr A D f)

lemma moduleHomotopyConeComp_second_hom {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    (moduleToHomotopy A D).map (moduleConeCompSecondMap A D f g) ≫
      (moduleToHomotopy A D).map (moduleConeCompHom A D f g) =
        (moduleToHomotopy A D).map (moduleConeInr A D (moduleConeCompMap A D f g)) := by
  let Q := moduleToHomotopy A D
  let e := moduleConeCompHomotopyIso A D f g
  have h : Q.map (moduleConeInr A D (moduleConeCompMap A D f g)) ≫ e.inv =
      Q.map (moduleConeCompSecondMap A D f g) := by
    change Q.map (moduleConeInr A D (moduleConeCompMap A D f g)) ≫
      Q.map (moduleConeCompInv A D f g) = Q.map (moduleConeCompSecondMap A D f g)
    rw [← Q.map_comp, moduleConeComp_inr_inv]
  change Q.map (moduleConeCompSecondMap A D f g) ≫ e.hom = _
  rw [← h, Category.assoc, e.inv_hom_id, Category.comp_id]

/-- 合成cone三角形は最初のcone射の標準cone三角形と同型。 -/
def moduleHomotopyConeCompTriangleIso {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    moduleHomotopyConeCompTriangle A D f g ≅
      moduleHomotopyConeTriangle A D (moduleConeCompMap A D f g) := by
  let Q := moduleToHomotopy A D
  refine Triangle.isoMk _ _ (Iso.refl (Q.obj (moduleCone A D f)))
    (Iso.refl (Q.obj (moduleCone A D (f ≫ g)))) (moduleConeCompHomotopyIso A D f g) ?_ ?_ ?_
  · change Q.map (moduleConeCompMap A D f g) ≫ 𝟙 _ =
      𝟙 _ ≫ Q.map (moduleConeCompMap A D f g)
    rw [Category.comp_id, Category.id_comp]
  · change Q.map (moduleConeCompSecondMap A D f g) ≫ Q.map (moduleConeCompHom A D f g) =
      𝟙 _ ≫ Q.map (moduleConeInr A D (moduleConeCompMap A D f g))
    rw [Category.id_comp]
    exact moduleHomotopyConeComp_second_hom A D f g
  · change (Q.map (moduleConeConnecting A D g ≫ (moduleConeInr A D f)⟦(1 : ℤ)⟧') ≫
      (Q.commShiftIso (1 : ℤ)).hom.app (moduleCone A D f)) ≫
        (𝟙 (Q.obj (moduleCone A D f)))⟦(1 : ℤ)⟧' =
      Q.map (moduleConeCompHom A D f g) ≫
        (Q.map (moduleConeConnecting A D (moduleConeCompMap A D f g)) ≫
          (Q.commShiftIso (1 : ℤ)).hom.app (moduleCone A D f))
    have h := (Q.map_comp (moduleConeCompHom A D f g)
      (moduleConeConnecting A D (moduleConeCompMap A D f g))).symm.trans
        (congrArg (fun a => Q.map a) (moduleConeComp_hom_connecting A D f g))
    apply triangle_comp_shift_id_of_eq
    exact (congrArg (fun a => a ≫ (Q.commShiftIso (1 : ℤ)).hom.app (moduleCone A D f))
      h.symm).trans (Category.assoc _ _ _)

lemma moduleHomotopyConeCompTriangle_distinguished {M N P : ModuleCategory A D}
    (f : M ⟶ N) (g : N ⟶ P) :
    moduleHomotopyConeCompTriangle A D f g ∈ moduleDistinguishedTriangles A D :=
  ⟨moduleCone A D f, moduleCone A D (f ≫ g), moduleConeCompMap A D f g,
    ⟨moduleHomotopyConeCompTriangleIso A D f g⟩⟩

end SerrePositivity.DifferentialGraded
end

end ConeCompositionTriangle

/-! ## Pretriangulated（旧 SerrePositivity/DifferentialGraded/Module/Pretriangulated.lean） -/

/-! # 全dg自然なconeによるK(D)のpretriangulated構造

三角形のクラスは既存の標準cone三角形の同型閉包そのもの。
-/

@[expose] public section Pretriangulated
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleDistinguished_invRotate (T : Triangle (ModuleHomotopyCategory A D))
    (hT : T ∈ moduleDistinguishedTriangles A D) :
    T.invRotate ∈ moduleDistinguishedTriangles A D :=
  moduleDistinguished_isomorphic A D _
    (moduleDistinguished_shift A D _
      (moduleDistinguished_rotate A D _ (moduleDistinguished_rotate A D T hT)) (-1)) _
    ((invRotateIsoRotateRotateShiftFunctorNegOne _).app T)

lemma moduleDistinguished_rotate_iff (T : Triangle (ModuleHomotopyCategory A D)) :
    T ∈ moduleDistinguishedTriangles A D ↔ T.rotate ∈ moduleDistinguishedTriangles A D := by
  constructor
  · exact moduleDistinguished_rotate A D T
  · intro hT
    exact moduleDistinguished_isomorphic A D _
      (moduleDistinguished_invRotate A D T.rotate hT) _ ((triangleRotation _).unitIso.app T)

instance moduleHomotopyPretriangulated : Pretriangulated (ModuleHomotopyCategory A D) where
  distinguishedTriangles := moduleDistinguishedTriangles A D
  isomorphic_distinguished := moduleDistinguished_isomorphic A D
  contractible_distinguished := moduleDistinguished_contractible A D
  distinguished_cocone_triangle := moduleDistinguished_cocone A D
  rotate_distinguished_triangle := moduleDistinguished_rotate_iff A D
  complete_distinguished_triangle_morphism := moduleDistinguished_complete A D

lemma moduleHomotopy_distinguished_iff (T : Triangle (ModuleHomotopyCategory A D)) :
    T ∈ distTriang (ModuleHomotopyCategory A D) ↔
      T ∈ moduleDistinguishedTriangles A D := Iff.rfl

end SerrePositivity.DifferentialGraded
end

end Pretriangulated

/-! ## Triangulated（旧 SerrePositivity/DifferentialGraded/Module/Triangulated.lean） -/

/-! # 全dg自然な合成cone比較によるK(D)の八面体公理 -/

@[expose] public section Triangulated
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance moduleHomotopyIsTriangulated : IsTriangulated (ModuleHomotopyCategory A D) :=
  IsTriangulated.mk' (by
    rintro ⟨M : ModuleCategory A D⟩ ⟨N : ModuleCategory A D⟩ ⟨P : ModuleCategory A D⟩ f' g'
    let Q := moduleToHomotopy A D
    obtain ⟨f, rfl⟩ := Q.map_surjective f'
    obtain ⟨g, rfl⟩ := Q.map_surjective g'
    refine ⟨Q.obj M, Q.obj N, Q.obj P, Q.obj (moduleCone A D f), Q.obj (moduleCone A D g),
      Q.obj (moduleCone A D (f ≫ g)), Q.map f, Q.map g,
      Iso.refl _, Iso.refl _, Iso.refl _, by simp, by simp,
      _, _, moduleHomotopyConeTriangle_distinguished A D f,
      _, _, moduleHomotopyConeTriangle_distinguished A D g,
      _, _, moduleHomotopyConeTriangle_distinguished A D (f ≫ g), ⟨?_⟩⟩
    let α := moduleConeTriangleMap A D f (f ≫ g) (𝟙 M) g (by rw [Category.id_comp])
    let β := moduleConeTriangleMap A D (f ≫ g) g f (𝟙 P) (by rw [Category.comp_id])
    refine Triangulated.Octahedron.mk (Q.map α.hom₃) (Q.map β.hom₃) ?_ ?_ ?_ ?_ ?_
    · exact (Q.mapTriangle.map α).comm₂
    · exact (Q.mapTriangle.map α).comm₃.symm.trans (by
        change (Q.map (moduleConeConnecting A D f) ≫ (Q.commShiftIso (1 : ℤ)).hom.app M) ≫
          (Q.map (𝟙 M))⟦(1 : ℤ)⟧' = _
        rw [Q.map_id M, (shiftFunctor (ModuleHomotopyCategory A D) (1 : ℤ)).map_id (Q.obj M)]
        exact Category.comp_id _)
    · exact (Q.mapTriangle.map β).comm₂.trans (by
        change Q.map (𝟙 P) ≫ Q.map (moduleConeInr A D g) = Q.map (moduleConeInr A D g)
        rw [Q.map_id P]
        exact Category.id_comp _)
    · exact (Q.mapTriangle.map β).comm₃
    · refine isomorphic_distinguished _ (moduleHomotopyConeCompTriangle_distinguished A D f g) _ ?_
      change Triangle.mk (Q.map (moduleConeCompMap A D f g))
        (Q.map (moduleConeCompSecondMap A D f g))
        ((moduleHomotopyConeTriangle A D g).mor₃ ≫
          (moduleHomotopyConeTriangle A D f).mor₂⟦(1 : ℤ)⟧') ≅
            moduleHomotopyConeCompTriangle A D f g
      exact eqToIso (congrArg (fun c => Triangle.mk (Q.map (moduleConeCompMap A D f g))
        (Q.map (moduleConeCompSecondMap A D f g)) c) (moduleHomotopyConeComp_mor₃ A D f g).symm))

end SerrePositivity.DifferentialGraded
end

end Triangulated

/-! ## HomotopyEvaluationTriangles（旧 SerrePositivity/DifferentialGraded/Module/HomotopyEvaluationTriangles.lean） -/

/-! # K(D)の評価関手によるdistinguished三角形の保存 -/

@[expose] public section HomotopyEvaluationTriangles
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated

/-- shiftと可換な関手の可換squareから三角形の比較を得る。 -/
def mapTriangleSquareIso {C E K H : Type*} [Category* C] [Category* E] [Category* K] [Category* H]
    [HasShift C ℤ] [HasShift E ℤ] [HasShift K ℤ] [HasShift H ℤ]
    (Q : C ⥤ K) (G : K ⥤ H) (F : C ⥤ E) (q : E ⥤ H)
    [Q.CommShift ℤ] [G.CommShift ℤ] [F.CommShift ℤ] [q.CommShift ℤ]
    (α : Q ⋙ G ≅ F ⋙ q) [NatTrans.CommShift α.hom ℤ]
    (T : Triangle C) (T' : Triangle E) (e : F.mapTriangle.obj T ≅ T') :
    G.mapTriangle.obj (Q.mapTriangle.obj T) ≅ q.mapTriangle.obj T' :=
  (Functor.mapTriangleCompIso Q G).symm.app T ≪≫
    (Functor.mapTriangleIso α).app T ≪≫
    (Functor.mapTriangleCompIso F q).app T ≪≫ q.mapTriangle.mapIso e

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 商に降ろした評価の因子分解同型。 -/
def moduleHomotopyEvaluationFacIso (x : D) :
    moduleToHomotopy A D ⋙ moduleHomotopyEvaluation A D x ≅
      moduleEvaluation A D x ⋙ _root_.HomotopyCategory.quotient (ModuleCat A) (.up ℤ) := by
  unfold moduleHomotopyEvaluation
  exact Quotient.lift.isLift _ _ _

instance moduleHomotopyEvaluationFacIsoCommShift (x : D) :
    NatTrans.CommShift (moduleHomotopyEvaluationFacIso A D x).hom ℤ := by
  unfold moduleHomotopyEvaluationFacIso moduleHomotopyEvaluation
  apply Quotient.liftCommShift_compatibility

/-- 評価されたK(D)の標準cone三角形と既存複体の標準cone三角形の比較。 -/
def moduleHomotopyConeTriangleEvaluationIso {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :=
  mapTriangleSquareIso (moduleToHomotopy A D) (moduleHomotopyEvaluation A D x)
    (moduleEvaluation A D x) (_root_.HomotopyCategory.quotient (ModuleCat A) (.up ℤ))
    (moduleHomotopyEvaluationFacIso A D x) (moduleConeTriangle A D f)
    (CochainComplex.mappingCone.triangle ((moduleEvaluation A D x).map f))
    (moduleConeTriangleEvaluationIso A D f x)

instance moduleHomotopyEvaluationIsTriangulated (x : D) :
    (moduleHomotopyEvaluation A D x).IsTriangulated where
  map_distinguished T hT := by
    change T ∈ moduleDistinguishedTriangles A D at hT
    obtain ⟨M, N, f, ⟨e⟩⟩ := hT
    exact isomorphic_distinguished _
      (_root_.HomotopyCategory.mappingCone_triangleh_distinguished
        ((moduleEvaluation A D x).map f)) _
      ((moduleHomotopyEvaluation A D x).mapTriangle.mapIso e ≪≫
        moduleHomotopyConeTriangleEvaluationIso A D f x)

end SerrePositivity.DifferentialGraded
end

end HomotopyEvaluationTriangles

/-! ## HomotopyConeEndpointTransport（旧 SerrePositivity/DifferentialGraded/Module/HomotopyConeEndpointTransport.lean） -/

/-!
概要：加群のホモトピー同型による端点変更を、同じ標準 cone の同型へ延長する。
方針：商関手の充満性で実閉射を選び、標準 distinguished triangle の二頂点比較を使う。
規約：端点の同型はホモトピー圏に置き、実加群の厳密同型を仮定しない。
使われ方：κ-small 提示の同時精密化で、代表化後の実閉射と cone を回収する。
-/

@[expose] public section HomotopyConeEndpointTransport
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Pretriangulated
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {M N M' N' : ModuleCategory R D}

lemma moduleHomotopyCone_transport_endpoints (f : M ⟶ N)
    (eM : (moduleToHomotopy R D).obj M ≅ (moduleToHomotopy R D).obj M')
    (eN : (moduleToHomotopy R D).obj N ≅ (moduleToHomotopy R D).obj N') :
    ∃ g : M' ⟶ N', Nonempty ((moduleToHomotopy R D).obj (moduleCone R D f) ≅
      (moduleToHomotopy R D).obj (moduleCone R D g)) := by
  let K := moduleToHomotopy R D
  obtain ⟨g, hg⟩ := K.map_surjective (eM.inv ≫ K.map f ≫ eN.hom)
  have hcomm : K.map f ≫ eN.hom = eM.hom ≫ K.map g := by
    rw [hg]
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  exact ⟨g, ⟨(Triangle.π₃).mapIso (isoTriangleOfIso₁₂
    (moduleHomotopyConeTriangle R D f) (moduleHomotopyConeTriangle R D g)
    (moduleHomotopyConeTriangle_distinguished R D f)
    (moduleHomotopyConeTriangle_distinguished R D g) eM eN hcomm)⟩⟩

end SerrePositivity.DifferentialGraded
end

end HomotopyConeEndpointTransport

/-! ## AcyclicTriangulated（旧 SerrePositivity/DifferentialGraded/Module/AcyclicTriangulated.lean） -/

/-! # K(D)のacyclic部分圏とVerdier局所化の射のクラス -/

@[expose] public section AcyclicTriangulated
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated ZeroObject
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance moduleHomotopyAcyclicClosedUnderIso :
    (moduleHomotopyAcyclic A D).IsClosedUnderIsomorphisms where
  of_iso e h x := (_root_.HomotopyCategory.subcategoryAcyclic (ModuleCat A)).prop_of_iso
    ((moduleHomotopyEvaluation A D x).mapIso e) (h x)

instance moduleHomotopyAcyclicContainsZero : (moduleHomotopyAcyclic A D).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, fun x =>
    (_root_.HomotopyCategory.subcategoryAcyclic (ModuleCat A)).prop_of_isZero
      ((moduleHomotopyEvaluation A D x).map_isZero (isZero_zero _))⟩

instance moduleHomotopyAcyclicStableShift : (moduleHomotopyAcyclic A D).IsStableUnderShift ℤ where
  isStableUnderShiftBy s := ⟨fun M h x =>
    ((_root_.HomotopyCategory.subcategoryAcyclic (ModuleCat A)).inverseImage
      (moduleHomotopyEvaluation A D x)).le_shift s M (h x)⟩

instance moduleHomotopyAcyclicTriangulatedClosed₂ :
    (moduleHomotopyAcyclic A D).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.mk' (P := moduleHomotopyAcyclic A D) (by
    intro T hT h₁ h₃ x
    exact (_root_.HomotopyCategory.subcategoryAcyclic (ModuleCat A)).ext_of_isTriangulatedClosed₂
      ((moduleHomotopyEvaluation A D x).mapTriangle.obj T)
      ((moduleHomotopyEvaluation A D x).map_distinguished T hT) (h₁ x) (h₃ x))

/-- 評価先のacyclic部分圏の逆像の共通部分は三角閉。 -/
instance moduleHomotopyAcyclicIsTriangulated : (moduleHomotopyAcyclic A D).IsTriangulated where

/-- Verdier局所化の射は、既に指定したobjectwise準同型そのもの。 -/
lemma moduleHomotopyAcyclic_trW_eq :
    (moduleHomotopyAcyclic A D).trW = moduleHomotopyQuasiIso A D := by
  ext M N f
  obtain ⟨M⟩ := M
  obtain ⟨N⟩ := N
  obtain ⟨f, rfl⟩ := (moduleToHomotopy A D).map_surjective f
  exact ((moduleHomotopyAcyclic A D).trW_iff_of_distinguished
    (moduleHomotopyConeTriangle A D f) (moduleHomotopyConeTriangle_distinguished A D f)).trans
      (moduleHomotopyQuasiIso_iff_acyclic_cone A D f).symm

end SerrePositivity.DifferentialGraded
end

end AcyclicTriangulated
