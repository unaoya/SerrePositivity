module

public import SerrePositivity.KST.DerivedGeometry.TensorBaseChange
public import SerrePositivity.KST.DerivedGeometry.CoefficientTensorPresheaf
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# 一般の基礎環に対するアフィン係数テンソル

概要：A → R に沿い H を底変換してから切断環へ送る二段のテンソルを比較する。
方針：切断のスカラー作用の塔を明示し、非可換係数の環同型を適用する。
規約：各開の前層切断について述べ、層条件や導来圏の比較を仮定しない。
使われ方：KST D4、Toën Derived Azumaya §3.2 のアフィン係数環層。
-/

@[expose] public section

noncomputable section

set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

namespace SerrePositivity.KST.DerivedGeometry

variable (A : Type u) [CommRing A] (R : CommRingCat.{u}) [Algebra A R]

/--
概要：A → R から Spec R の大域切断への基礎環写像を得る。
方針：標準の大域切断の同型の逆と A → R を合成する。
規約：A と R の作用を同一視せず合成を明示する。
使われ方：KST D4、Toën §3.2 の一般のアフィン係数。
-/
def affineBaseMap : A →+* Γ(Spec R, ⊤) :=
  (Scheme.ΓSpecIso R).inv.hom.comp (algebraMap A R)

/--
概要：Spec の構造射から得る基礎環写像は affineBaseMap と一致する。
方針：Spec の大域切断の同型の逆の自然性を使う。
規約：構造射は A → R の algebraMap の Spec とする。
使われ方：KST D4、Toën §3.2 の実際の構造射との接続。
-/
lemma globalBaseMap_spec :
    globalBaseMap (Spec.map (CommRingCat.ofHom (algebraMap A R))) =
      affineBaseMap A R := by
  exact (congrArg CommRingCat.Hom.hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A R)))).symm

/--
概要：切断上の A 作用は R を経由するスカラーの塔を成す。
方針：二つの基礎環写像の定義を展開して合成の一致を確認する。
規約：テンソル前層で用いる sectionAlgebra を両方の作用に指定する。
使われ方：KST D4、Toën §3.2 の二段の係数底変換。
-/
theorem affineBaseSectionScalarTower (U : (Spec R).Opens) :
    letI := sectionAlgebra (Scheme.ΓSpecIso R).inv.hom U
    letI := sectionAlgebra (affineBaseMap A R) U
    IsScalarTower A R Γ(Spec R, U) := by
  let := sectionAlgebra (Scheme.ΓSpecIso R).inv.hom U
  let := sectionAlgebra (affineBaseMap A R) U
  exact IsScalarTower.of_algebraMap_eq' rfl

variable (H : Type u) [Ring H] [Algebra A H]

/--
概要：各開で二段の係数テンソルと A 上の一段のテンソルを環として同定する。
方針：明示したスカラーの塔に右側の底変換の環同型を適用する。
規約：底変換 H ⊗_A R は右因子により R 代数とする。
使われ方：KST D4、Toën §3.2 の係数前層の自然同型の成分。
-/
def affineCoefficientBaseChangeIsoAt (U : (Spec R).Opens) :
    letI : Algebra R (H ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
    (coefficientTensorPresheaf (H ⊗[A] R) (Scheme.ΓSpecIso R).inv.hom).obj (.op U) ≅
      (coefficientTensorPresheaf H (affineBaseMap A R)).obj (.op U) := by
  letI : Algebra R (H ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
  letI (V : (Spec R).Opens) := sectionAlgebra (Scheme.ΓSpecIso R).inv.hom V
  letI (V : (Spec R).Opens) := sectionAlgebra (affineBaseMap A R) V
  letI (V : (Spec R).Opens) := affineBaseSectionScalarTower A R V
  exact (tensorBaseChangeRight A R Γ(Spec R, U) H).toRingCatIso

/--
概要：二段の係数テンソルと一段の係数テンソルの前層は自然同型。
方針：切断ごとの環同型を用い、制限への自然性を底変換の一般計算から得る。
規約：基礎環の作用は affineBaseMap によって指定する。
使われ方：KST D4、Toën §3.2 のアフィン係数環層の底変換。
-/
def affineCoefficientBaseChangeIso :
    letI : Algebra R (H ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
    coefficientTensorPresheaf (H ⊗[A] R) (Scheme.ΓSpecIso R).inv.hom ≅
      coefficientTensorPresheaf H (affineBaseMap A R) := by
  letI : Algebra R (H ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
  letI (V : (Spec R).Opens) := sectionAlgebra (Scheme.ΓSpecIso R).inv.hom V
  letI (V : (Spec R).Opens) := sectionAlgebra (affineBaseMap A R) V
  letI (V : (Spec R).Opens) := affineBaseSectionScalarTower A R V
  refine NatIso.ofComponents (fun U => affineCoefficientBaseChangeIsoAt A R H U.unop) ?_
  intro U V i
  apply RingCat.hom_ext
  apply RingHom.ext
  intro x
  exact tensorBaseChangeRight_naturality A R Γ(Spec R, U.unop) H
    (sectionRestriction (Scheme.ΓSpecIso R).inv.hom i.unop) x

/--
概要：係数前層の底変換の同型は構造層からの単位と可換。
方針：各開で底変換の同型が右因子への包含を保つことを使う。
規約：構造層の射を指定されたものとして保つ。
使われ方：KST D4、Toën §3.2 の正則 O 加群の比較。
-/
lemma affineCoefficientBaseChangeIso_unit :
    letI : Algebra R (H ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
    coefficientTensorUnit (H ⊗[A] R) (Scheme.ΓSpecIso R).inv.hom ≫
      (affineCoefficientBaseChangeIso A R H).hom =
    coefficientTensorUnit H (affineBaseMap A R) := by
  let : Algebra R (H ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
  let (V : (Spec R).Opens) := sectionAlgebra (Scheme.ΓSpecIso R).inv.hom V
  let (V : (Spec R).Opens) := sectionAlgebra (affineBaseMap A R) V
  let (V : (Spec R).Opens) := affineBaseSectionScalarTower A R V
  apply NatTrans.ext
  funext U
  apply RingCat.hom_ext
  apply RingHom.ext
  intro s
  exact tensorBaseChangeRight_unit A R Γ(Spec R, U.unop) H s

end SerrePositivity.KST.DerivedGeometry
