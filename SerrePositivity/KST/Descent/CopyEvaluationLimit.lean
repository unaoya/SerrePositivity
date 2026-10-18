module

public import SerrePositivity.KST.Descent.CopyComparison
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.Algebra.Module.ULift
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# 積の普遍性からコピー比較の全単射性へ

## 概要
前層を適用したコピーの錐が積の普遍性を持てば、指定評価写像が全単射になることを証明する。
有限非交和の普遍性と反対圏の積の保存から、この条件を供給できる。

## 方針
積の普遍性を有理数の自由加群からの射で検査する。
係数の宇宙に合わせた ULift ℚ を用いて、添字型の宇宙に制約を加えない。

## 規約
ここで用いる通常の積は有限非交和の値の比較に限る。
通常の極限を Čech Tot やホモトピー引き戻しの代わりには使わない。
前層の積保存は、実際の Zariski 降下から供給する別の責務。

## 使われ方
論文 (3.8) のコピー評価の全単射性と、実際の非交和の普遍性の接続。
-/

@[expose] public section

universe u v w t

open CategoryTheory CategoryTheory.Limits Opposite

namespace SerrePositivity.KST.Descent

/-- 概要：一つの元を有理数の自由加群からの射で指定する（論文 (3.8) の補助）。
方針：スカラー倍の線形写像を宇宙を持ち上げた有理数から構成する。
規約：この射は 1 を指定元へ送る。
使われ方：コピーの錐の普遍性で個々の元を検査する。 -/
def copyScalarProbe {M : ModuleCat.{t} ℚ} (x : M) : ModuleCat.of ℚ (ULift.{t} ℚ) ⟶ M :=
  ModuleCat.ofHom ((LinearMap.toSpanSingleton ℚ M x).comp ULift.moduleEquiv.toLinearMap)

/-- 概要：自由加群からの指定射は 1 を指定元へ送る（論文 (3.8) の補助）。
方針：線形写像の定義と 1 のスカラー作用を計算する。
規約：ULift は宇宙の調整のみ。
使われ方：普遍性による比較を元の評価写像へ戻す。 -/
@[simp] theorem copyScalarProbe_one {M : ModuleCat.{t} ℚ} (x : M) :
    (copyScalarProbe x).hom (ULift.up 1) = x := by
  change (1 : ℚ) • x = x
  exact one_smul ℚ x

namespace GradedPresheaf

variable {C : Type u} [Category.{v} C] {Coefficient : Type w}
variable (L : GradedPresheaf.{u, v, w, t} C Coefficient)
variable {B W : C} {I : Type*}

/-- 概要：コピーへの制限の錐の積の普遍性から指定評価の全単射性（論文 (3.8)）。
方針：自由な有理加群からの射の一意性と存在を用い、元ごとの単射・全射を示す。
規約：比較を任意の抽象同型へ取り替えず、包含の引き戻しをそのまま使う。
使われ方：前層の有限積保存と指定されたコピー比較の接続。 -/
theorem copyEvaluation_bijective_of_isLimit (H : Coefficient) (n : ℤ)
    (inclusions : I → (B ⟶ W))
    (limit : IsLimit (Fan.mk ((L H n).obj (op W))
      (fun i ↦ (L H n).map (inclusions i).op))) :
    Function.Bijective (L.copyEvaluation H n inclusions) := by
  constructor
  · intro x y equal_evaluations
    have equal_probes : copyScalarProbe x = copyScalarProbe y := by
      apply limit.hom_ext
      rintro ⟨i⟩
      ext r
      change L.pullback H n (inclusions i) (r.down • x) =
        L.pullback H n (inclusions i) (r.down • y)
      rw [map_smul, map_smul]
      exact congrArg (fun z ↦ r.down • z) (congrFun equal_evaluations i)
    have h := congrArg (fun f ↦ f.hom (ULift.up 1)) equal_probes
    exact (copyScalarProbe_one x).symm.trans (h.trans (copyScalarProbe_one y))
  · intro values
    let cone := Fan.mk (ModuleCat.of ℚ (ULift.{t} ℚ)) (fun i ↦ copyScalarProbe (values i))
    refine ⟨(limit.lift cone).hom (ULift.up 1), ?_⟩
    funext i
    have h := congrArg (fun f ↦ f.hom (ULift.up 1)) (limit.fac cone (Discrete.mk i))
    change L.pullback H n (inclusions i) ((limit.lift cone).hom (ULift.up 1)) =
      (copyScalarProbe (values i)).hom (ULift.up 1) at h
    exact h.trans (copyScalarProbe_one _)

/-- 概要：非交和の普遍性と反対圏の積保存からコピー比較の全単射性（論文 (3.8)）。
方針：非交和の錐を反対圏の積の錐にし、前層による極限保存を適用する。
規約：積保存は明示的な条件で、前層の任意の極限保存は要求しない。
使われ方：実際の軌道の有限非交和の比較を (3.8) へ供給する。 -/
theorem copyEvaluation_bijective_of_preservesProduct (H : Coefficient) (n : ℤ)
    (inclusions : I → (B ⟶ W)) (colimit : IsColimit (Cofan.mk W inclusions))
    [PreservesLimit (Discrete.functor (fun _ : I ↦ op B)) (L H n)] :
    Function.Bijective (L.copyEvaluation H n inclusions) := by
  apply L.copyEvaluation_bijective_of_isLimit H n inclusions
  exact isLimitFanMkObjOfIsLimit (L H n) (fun _ : I ↦ op B)
    (fun i ↦ (inclusions i).op) (Cofan.IsColimit.op colimit)

end GradedPresheaf

end SerrePositivity.KST.Descent
