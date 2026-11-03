module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.LocalObjects.LocalityNaturalComparison
public import SerrePositivity.InfinityCategories.F2.Presentable.ColimitComparisonDetection
public import SerrePositivity.InfinityCategories.F1.Compact.HomCovariantComparison
public import SerrePositivity.InfinityCategories.F2.Compact.Preservation
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.CompactEndpoints

/-!
概要：端点が共通の濃度で compact な小さい辺族の局所性は filtered 余極限で閉じる。
方針：同じ全 Hom 自然比較の成分の可逆性を、保存された元の余極限から検出する。
規約：元の局所対象定義と元の全 coherent 図式・余錐を保持する。
使われ方：局所対象圏の filtered 余極限の存在・包含の保存性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization.LocalObjects
open HomotopyLimits

/-- 概要：指定辺の両端が compact なら局所対象の指定 filtered 余極限頂点も局所。
方針：元の全共変 Hom 自然比較の成分の可逆性を余極限へ送る。
規約：元の余錐と元の局所性を変更しない。
使われ方：小さい辺族の同時局所性の閉性。 -/
lemma isLocalForHom_colimit_of_compactEndpoints {κ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] {x y : C _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj C) x y)
    (hx : Compact.IsKappaCompact.{u, u + 1} κ x)
    (hy : Compact.IsKappaCompact.{u, u + 1} κ y)
    {K : SSet.{u}} [Quasicategory K] [IsKappaFiltered κ K]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C)
    (c : JoinCocone D) (hc : IsColimitCone c)
    (hD : ∀ k : K _⦋0⦌,
      IsLocalForHom (Truncated.HomotopyCategory.homMk e) (D.app _ (ULift.up k))) :
    IsLocalForHom (Truncated.HomotopyCategory.homMk e) c.vertex := by
  have hF := hy.of_functorIso (Compact.homInfinityCovariant_covariantIso y).symm
  have hG := hx.of_functorIso (Compact.homInfinityCovariant_covariantIso x).symm
  have h := functorHomEvaluate_isIso_of_colimit (JoinCocone.ulift c)
    (hF K D c hc) (hG K D c hc) (localPrecompositionComparison e) (by
      rintro ⟨⟨k⟩⟩
      exact (localPrecompositionComparison_isIso_iff e _).mpr (hD k))
  exact (localPrecompositionComparison_isIso_iff e c.vertex).mp h

/-- 概要：共通 compact 端点を持つ指定辺族の局所性は filtered 余極限で閉じる。
方針：元の局所性を各添字へ展開し、同じ辺の閉性を同時に使う。
規約：元の像集合の局所対象全部分圏を使用する。
使われ方：局所対象圏での同じ filtered 余極限の構成。 -/
lemma isLocalObject_colimit_of_compactEndpoints {κ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] {I : Type u} (edges : I → C _⦋1⦌)
    (hends : ∀ i, Compact.IsKappaCompact.{u, u + 1} κ (C.δ 1 (edges i)) ∧
      Compact.IsKappaCompact.{u, u + 1} κ (C.δ 0 (edges i)))
    {K : SSet.{u}} [Quasicategory K] [IsKappaFiltered κ K]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C)
    (c : JoinCocone D) (hc : IsColimitCone c)
    (hD : ∀ k : K _⦋0⦌, IsLocalObject (Set.range edges) (D.app _ (ULift.up k))) :
    IsLocalObject (Set.range edges) c.vertex := by
  rw [isLocalObject_range_iff]
  intro i
  exact isLocalForHom_colimit_of_compactEndpoints (edgeOfSimplex (edges i))
    (hends i).1 (hends i).2 D c hc
    (fun k ↦ (isLocalObject_range_iff edges _).mp (hD k) i)

end SerrePositivity.InfinityCategories.F2.Presentable.Localization.LocalObjects
