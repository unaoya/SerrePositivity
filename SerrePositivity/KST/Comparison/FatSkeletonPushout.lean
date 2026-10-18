module

public import SerrePositivity.KST.Comparison.FatSkeletonAttachment
public import SerrePositivity.KST.Comparison.FatRowComplement
public import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
# fat realization の有限骨格の付着の pushout

概要：n+1 骨格は n 骨格へ新しい行の標準単体を境界に沿って貼り付けた pushout である。
方針：全射な標準形の次元による被覆、境界の引き戻し、境界外の単射性を各次数で使う。
規約：Segal 1974 Proposition 1.6 の実際の有限骨格の付着の普遍性。
使われ方：二重写像円筒の貼り合わせとの比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial

/--
概要：次の骨格の各元は、旧骨格または新しい行の元から得られる。
方針：正規化の次元が旧上限以下か、新しい次元に等しいかで分ける。
規約：型の圏の pushout 判定に使う共同全射性。
使われ方：有限骨格の付着の普遍性の全射側。
-/
theorem fatSkeletonStep_row_jointly_surjective
    (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ) (d : SimplexCategoryᵒᵖ) :
    Set.range ((fatSkeletonStep F n).app d) ⊔
      Set.range ((fatSkeletonRow F (n + 1)).app d) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  by_cases h : (fatDegreeNormalize F d y.1).degree.len ≤ n
  · exact Or.inl ⟨⟨y.1, h⟩, Subtype.ext rfl⟩
  · have hy : (fatDegreeNormalize F d y.1).degree.len ≤ n + 1 := y.2
    have heq : (fatDegreeNormalize F d y.1).degree.len = n + 1 := by omega
    obtain ⟨x, t, ht⟩ := fatNormalFormRealize_eq_row F d (fatDegreeNormalize F d y.1) (n + 1) heq
    apply Or.inr
    refine ⟨(x, t), ?_⟩
    apply Subtype.ext
    exact ht.trans (fatNormalFormRealize_degreeNormalize F d y.1)

/--
概要：次の骨格は、旧骨格と新しい行の境界に沿う実際の pushout である。
方針：各次数の型で、厳密な引き戻し・共同全射性・境界外の単射性による判定を使う。
規約：ホモトピー pushout 性を入力として仮定せず、実対象の普遍性を示す。
使われ方：Segal Proposition 1.6 の有限骨格の帰納。
-/
theorem fatSkeleton_isPushout (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ) :
    IsPushout (fatBoundaryAttachment F n)
      (F.obj (op ⦋n + 1⦌) ◁ (SSet.boundary (n + 1)).ι)
      (fatSkeletonStep F n) (fatSkeletonRow F (n + 1)) := by
  apply IsPushout.of_forall_isPushout_app
  intro d
  let ev := (evaluation SimplexCategoryᵒᵖ (Type u)).obj d
  have hpb := (fatBoundaryAttachment_isPullback F n).map ev
  let : Mono ((fatSkeleton F n).ι.app d) :=
    (NatTrans.mono_iff_mono_app _).mp inferInstance d
  let : Mono ((fatSkeleton F (n + 1)).ι.app d) :=
    (NatTrans.mono_iff_mono_app _).mp inferInstance d
  apply Types.isPushout_of_isPullback_of_mono
    (k := (fatSkeleton F (n + 1)).ι.app d) hpb
    (congrArg (fun t => t.app d) (fatSkeletonStep_ι F n))
    (congrArg (fun t => t.app d) (fatSkeletonRow_ι F (n + 1)))
    (fatSkeletonStep_row_jointly_surjective F n d)
  exact fatRealizationInclusion_injective_off_boundary_range F (n + 1) d

end SerrePositivity.KST.Comparison
