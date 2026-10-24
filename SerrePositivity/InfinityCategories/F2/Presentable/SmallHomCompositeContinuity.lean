module

public import SerrePositivity.InfinityCategories.F2.Presentable.NativeUniverseReflection
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessibleSmallCovariantHom
public import SerrePositivity.InfinityCategories.F2.Presentable.ObjectCompactCardinals
public import SerrePositivity.InfinityCategories.F2.Compact.ColimitRetractions

/-!
概要：小さい共変 Hom 模型の関手との合成に accessibility と極限保存を移す。
方針：元の全 Hom の保存性を全自然同型で移し、指定宇宙変更の充満忠実性で反映する。
規約：宇宙変更の反映界面は明示入力であり、未証明の存在主張を含めない。
使われ方：Compact の供給界面から d3 の余表現可能性への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：元の小さい Hom 模型の合成は同じ大きい Hom 合成と全自然に一致する。
方針：元の比較を前合成し、宇宙変更との合成を結合し直す。
規約：元の関手 G と Hom 対象 x を保持する。
使われ方：保存性を小さい空間値の合成へ移す。 -/
def smallHomCompositeIso {X Y : SSet.{u + 1}} [Quasicategory X]
    (G : Y ⟶ X) (x : X _⦋0⦌) (H : X ⟶ SpaceInfinity.{u})
    (hH : FunctorIso (covariantRepresentableInfinity x)
      ((SSet.uliftFunctor.{u + 2, u + 1}).map H ≫ Compact.spaceUniverseDiagram)) :
    FunctorIso ((SSet.uliftFunctor.{u + 2, u + 1}).map G ≫ covariantRepresentableInfinity x)
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (G ≫ H) ≫ Compact.spaceUniverseDiagram) := by
  simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using
    FunctorIso.precomp hH ((SSet.uliftFunctor.{u + 2, u + 1}).map G)

/-- 概要：accessible な関手との小さい Hom 合成は、反映界面の下で accessible。
方針：元の Hom 対象の compact 濃度を取り、全 Hom 保存を比較して反映する。
規約：濃度は元の宇宙 u に取る。
使われ方：余表現可能性に必要な小さい解関手の accessibility。 -/
lemma smallHomComposite_isAccessible {X Y : SSet.{u + 1}} [Quasicategory X]
    (hU : IsFullyFaithful Compact.spaceUniverseDiagram.{u}) (hX : IsAccessible X)
    (G : Y ⟶ X) (hG : IsAccessibleFunctor G) (x : X _⦋0⦌)
    (H : X ⟶ SpaceInfinity.{u})
    (hH : FunctorIso (covariantRepresentableInfinity x)
      ((SSet.uliftFunctor.{u + 2, u + 1}).map H ≫ Compact.spaceUniverseDiagram)) :
    IsAccessibleFunctor (G ≫ H) := by
  obtain ⟨κ, _, hκG⟩ := hG
  obtain ⟨μ, hμ, hκμ, hx⟩ := hX.exists_compactCardinal x κ
  have hGμ : IsKappaAccessibleFunctor μ G := hκG.of_le hκμ.le
  have h := (hGμ.comp_universe hx).of_functorIso (smallHomCompositeIso G x H hH)
  exact ⟨μ, hμ, isKappaAccessibleFunctor_of_spaceUniverse hU h⟩

/-- 概要：極限保存関手との小さい Hom 合成は、反映界面の下で全小極限を保つ。
方針：元の Hom の全極限保存を比較で移し、同じ指定錐へ反映する。
規約：全ての元の小さい形状を保つ。
使われ方：d3 による Hom 合成の余表現可能性。 -/
lemma smallHomComposite_preservesSmallLimits {X Y : SSet.{u + 1}} [Quasicategory X]
    (hU : IsFullyFaithful Compact.spaceUniverseDiagram.{u})
    (G : Y ⟶ X) (hG : PreservesSmallLimits G) (x : X _⦋0⦌)
    (H : X ⟶ SpaceInfinity.{u})
    (hH : FunctorIso (covariantRepresentableInfinity x)
      ((SSet.uliftFunctor.{u + 2, u + 1}).map H ≫ Compact.spaceUniverseDiagram)) :
    PreservesSmallLimits (G ≫ H) := by
  apply preservesSmallLimits_of_spaceUniverse hU
  intro K D c hc
  have h := covariantRepresentableInfinity_isLimit (mapJoinCone G c) (hG K D c hc) x
  rw [← mapJoinCone_universe_comp] at h
  exact h.of_functorIso ((smallHomCompositeIso G x H hH).precomp (JoinCone.ulift c).val)

end SerrePositivity.InfinityCategories.F2.Presentable
