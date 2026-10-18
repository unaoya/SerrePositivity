module

public import SerrePositivity.KST.DerivedBlowup.ExteriorAssociativity
public import SerrePositivity.KST.DerivedBlowup.ChartCochainMaps
public import SerrePositivity.DifferentialGraded.Category.Basic

/-!
概要：KST Def3.1 の外積 Koszul dg 代数を既存の一対象 dg 圏として装備する。
方針：Hom 複体・単位・乗法と証明済みの圏法則を ofHomObjects に渡す。
規約：新しい dg 圏の公理構造は導入しない。反復 cone 模型との比較は別工程。
使われ方：導来 blowup と例外因子のチャート環の dg 加群圏。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- 概要：外積 Koszul 複体を Hom とする一対象 dg 圏。
方針：単位則・結合則を既存の豊穣圏 constructor に渡す。
規約：KST Def3.1、対象は Unit。使われ方：Koszul チャートの dg 加群。
-/
@[instance_reducible] def exteriorKoszulDGCategory (d : M →ₗ[R] R) :
    DifferentialGraded.DGCategory R Unit :=
  DifferentialGraded.ofHomObjects R Unit
    (fun _ _ => exteriorKoszulCochain d)
    (fun _ => exteriorKoszulUnit d)
    (fun _ _ _ => exteriorKoszulMultiplication d)
    (fun _ _ => exteriorKoszul_left_unit d)
    (fun _ _ => exteriorKoszul_right_unit d)
    (fun _ _ _ _ => exteriorKoszul_assoc d)

/-- 概要：一対象 dg 圏の Hom は指定した外積複体。
方針：constructor の定義を展開する。
規約：KST Def3.1。使われ方：チャートの underlying 複体の比較。 -/
theorem exteriorKoszulDGCategory_hom (d : M →ₗ[R] R) :
    (exteriorKoszulDGCategory d).Hom () () = exteriorKoszulCochain d := rfl

/-- 概要：Koszul 微分で添字付けした一対象型。
方針：異なる微分の dg 圏を同時に扱えるよう、対象型にも微分を保持する。
規約：KST Def3.1。使われ方：チャート間 dg 関手の型クラス解決。 -/
inductive ExteriorKoszulObject (d : M →ₗ[R] R) : Type u
  | point

/-- 概要：微分で添字付けした一対象型の Koszul dg 圏構造。
方針：構成済みの Hom・単位・乗法と圏法則を用いる。
規約：KST Def3.1。使われ方：異なるチャートの dg 圏を同時に使う。 -/
instance exteriorKoszulObjectDGCategory (d : M →ₗ[R] R) :
    DifferentialGraded.DGCategory R (ExteriorKoszulObject d) :=
  DifferentialGraded.ofHomObjects R (ExteriorKoszulObject d)
    (fun _ _ => exteriorKoszulCochain d)
    (fun _ => exteriorKoszulUnit d)
    (fun _ _ _ => exteriorKoszulMultiplication d)
    (fun _ _ => exteriorKoszul_left_unit d)
    (fun _ _ => exteriorKoszul_right_unit d)
    (fun _ _ _ _ => exteriorKoszul_assoc d)

/-- 概要：導来 blowup チャートの外積模型による一対象 dg 圏。
方針：生成元の微分 a_i x_j−a_j の Koszul dg 代数を使う。
規約：KST Def3.1、基底環上の規格化座標。使われ方：チャート図式の局所環。
-/
@[instance_reducible] def chartExteriorDGCategory {I : Type u} [DecidableEq I]
    (a x : I → R) (i : I) :
    DifferentialGraded.DGCategory R Unit :=
  exteriorKoszulDGCategory (chartKoszulDifferential a x i)

/-- 概要：例外因子チャートの外積模型による一対象 dg 圏。
方針：pivot 方程式と残りの関係式に対応する Koszul 微分を使う。
規約：KST Lemma3.6。使われ方：E∩U_i の局所 dg 環。
-/
@[instance_reducible] def exceptionalExteriorDGCategory {I : Type u} [DecidableEq I]
    (a x : I → R) (i : I) :
    DifferentialGraded.DGCategory R Unit :=
  exteriorKoszulDGCategory (Finsupp.linearCombination R (exceptionalRelationValue a x i))

end SerrePositivity.KST.DerivedBlowup
