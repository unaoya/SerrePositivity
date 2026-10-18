module

public import SerrePositivity.KST.Descent.ClosedImmersionSquare
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# 有限型の圏内の非交和と閉中心の普遍性

## 概要
スキームの非交和の普遍性を有限型の圏へ反映し、閉中心の引き戻しの持ち上げを構成する。

## 方針
非交和は Over の忘却と充満部分圏の余極限の反映を使う。
引き戻しへの射は、構造射との両立を第一射影で確認して持ち上げる。

## 規約
有限型の圏内の任意の極限・余極限の存在は仮定しない。
ここで構成した具体的な対象の普遍性だけを証明する。

## 使われ方
論文 定理 3.1 の例外部分を中心のコピーの非交和として構成する。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

/-- 概要：スキームとしての非交和の普遍性を有限型の圏へ反映（論文 (3.8)）。
方針：Over の忘却と充満部分圏の包含による余極限の反映を用いる。
規約：成分と余錐点が有限型であることは型で保持する。
使われ方：例外部分の実際のスキームの非交和から前層の定義域の非交和へ移す。 -/
noncomputable def finiteTypeCofanIsColimitOfSchemeIsColimit {S : Scheme.{u}}
    {I : Type*} {X : I → FiniteTypeSchemes S} {W : FiniteTypeSchemes S}
    (inclusions : ∀ i, X i ⟶ W)
    (h : IsColimit (Cofan.mk W.obj.left (fun i ↦ (inclusions i).hom.left))) :
    IsColimit (Cofan.mk W inclusions) := by
  let F := ObjectProperty.ι
    (fun X : Over S ↦ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom) ⋙ Over.forget S
  apply isColimitOfReflects F
  exact (isColimitMapCoconeCofanMkEquiv F X inclusions).symm h

variable {S : Scheme.{u}} {X Y Z T : FiniteTypeSchemes S}
variable (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i.hom.left]

/-- 概要：可換な二射を閉中心の引き戻しへ持ち上げる（論文 定理 3.1）。
方針：実際のスキームの引き戻しへ持ち上げ、第一射影で構造射の可換性を確認する。
規約：有限型の圏内の射として構成する。
使われ方：例外部分の各コピーの包含。 -/
noncomputable def closedImmersionPullbackLift (a : T ⟶ Y) (b : T ⟶ Z)
    (comm : a ≫ f = b ≫ i) : T ⟶ closedImmersionPullback f i :=
  ObjectProperty.homMk (Over.homMk
    (pullback.lift a.hom.left b.hom.left (congrArg (fun k ↦ k.hom.left) comm)) (by
      change pullback.lift a.hom.left b.hom.left _ ≫
        (pullback.fst f.hom.left i.hom.left ≫ Y.obj.hom) = T.obj.hom
      rw [pullback.lift_fst_assoc, a.hom.w]))

/-- 概要：閉中心の引き戻しへの持ち上げの第一射影（論文 定理 3.1）。
方針：忘却後に引き戻しの合成公式を使う。
規約：有限型の圏内の等式。
使われ方：例外部分の包含と軌道のコピーの両立。 -/
@[reassoc (attr := simp)] theorem closedImmersionPullbackLift_fst
    (a : T ⟶ Y) (b : T ⟶ Z) (comm : a ≫ f = b ≫ i) :
    closedImmersionPullbackLift f i a b comm ≫ (closedImmersionSquare f i).f₁₂ = a := by
  apply ObjectProperty.hom_ext
  apply (Over.forget S).map_injective
  exact pullback.lift_fst _ _ _

/-- 概要：閉中心の引き戻しへの持ち上げの第二射影（論文 定理 3.1）。
方針：忘却後に引き戻しの合成公式を使う。
規約：有限型の圏内の等式。
使われ方：例外部分の包含と中心への射の両立。 -/
@[reassoc (attr := simp)] theorem closedImmersionPullbackLift_snd
    (a : T ⟶ Y) (b : T ⟶ Z) (comm : a ≫ f = b ≫ i) :
    closedImmersionPullbackLift f i a b comm ≫ (closedImmersionSquare f i).f₁₃ = b := by
  apply ObjectProperty.hom_ext
  apply (Over.forget S).map_injective
  exact pullback.lift_snd _ _ _

/-- 概要：閉中心の具体的な正方形は有限型の圏内でも引き戻し（論文 §3）。
方針：構成した持ち上げの二射影と、スキームの引き戻しの一意性を使う。
規約：スキームとしての Cartesian 性に加えて前層の定義域内の普遍性も示す。
使われ方：例外部分とそのコピーを扱う普遍性の計算。 -/
theorem closedImmersionSquare_isPullback :
    IsPullback (closedImmersionSquare f i).f₁₂ (closedImmersionSquare f i).f₁₃ f i := by
  apply IsPullback.of_isLimit (c := PullbackCone.mk (closedImmersionSquare f i).f₁₂
    (closedImmersionSquare f i).f₁₃ (closedImmersionSquare f i).fac)
  refine PullbackCone.IsLimit.mk (closedImmersionSquare f i).fac
    (fun s ↦ closedImmersionPullbackLift f i s.fst s.snd s.condition)
    (fun s ↦ closedImmersionPullbackLift_fst f i s.fst s.snd s.condition)
    (fun s ↦ closedImmersionPullbackLift_snd f i s.fst s.snd s.condition) ?_
  intro s m hm₁ hm₂
  apply ObjectProperty.hom_ext
  apply (Over.forget S).map_injective
  apply pullback.hom_ext
  · exact (congrArg (fun k ↦ k.hom.left) hm₁).trans
      (congrArg (fun k ↦ k.hom.left)
        (closedImmersionPullbackLift_fst f i s.fst s.snd s.condition)).symm
  · exact (congrArg (fun k ↦ k.hom.left) hm₂).trans
      (congrArg (fun k ↦ k.hom.left)
        (closedImmersionPullbackLift_snd f i s.fst s.snd s.condition)).symm

end SerrePositivity.KST.Descent
