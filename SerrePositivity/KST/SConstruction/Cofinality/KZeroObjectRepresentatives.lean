module
public import SerrePositivity.KST.SConstruction.Cofinality.WideKZeroObstruction
public import SerrePositivity.KST.LocalizingInvariants.CompletionZeroComponent

/-!
概要：同じ全多次数の三角圏 K₀ の全類を一つの対象で表す。
方針：自由アーベル群の表示で帰納し、和を双積、負号を一回シフトで表す。
規約：主経路に compact 性や冪等完備性を追加しない。
使われ方：wide 成分から K₀ 余核への比較の全射性。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory Limits Pretriangulated SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial ZeroObject

/-- 概要：同じ反復 S の三角圏 K₀ の全類は一つのホモトピー圏の対象の類である。
方針：零・対象・負の対象・和について自由アーベル群の表示で帰納する。
規約：双積と一回シフトは元の安定ホモトピー圏のもの。
使われ方：K₀ 余核の全類へ到達する頂点を選ぶ。 -/
lemma completionKZeroClass_representable (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    (Y : StableModel.{u})
    (z : TriangulatedK0 (hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier)) :
    ∃ y : hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier,
      TriangulatedK0.mk y = z := by
  let C := hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier
  refine Quotient.inductionOn z ?_
  intro a
  induction a using FreeAbelianGroup.induction_on with
  | zero => exact ⟨(0 : C), TriangulatedK0.mk_zero⟩
  | of y => exact ⟨y, rfl⟩
  | neg y _ =>
    refine ⟨(shiftFunctor C (1 : ℤ)).obj y, ?_⟩
    exact (TriangulatedK0.mk_shift_one y).trans (QuotientAddGroup.mk_neg _ _).symm
  | add a b ha hb =>
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hb
    refine ⟨x ⊞ y, ?_⟩
    have h := TriangulatedK0.mk_triangle (binaryBiproductTriangle x y)
      (binaryBiproductTriangle_distinguished x y)
    exact h.trans ((congrArg₂ (· + ·) hx hy).trans (QuotientAddGroup.mk_add _ a b).symm)

/-- 概要：元の同じ多次数の頂点の対象類は三角圏 K₀ へ全射。
方針：対象での表示とホモトピー圏の頂点表示を順に使う。
規約：元の quasicategory の実頂点で表す。
使われ方：wide の実頂点から余核類を回収する。 -/
lemma completionKZeroVertex_surjective (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    (Y : StableModel.{u}) :
    Function.Surjective (fun y : (((multiSEndofunctor r).obj ι).obj Y).carrier _⦋0⦌ =>
      TriangulatedK0.mk (C := hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier)
        (HomotopyCategory.mk y)) := by
  intro z
  obtain ⟨y, hy⟩ := completionKZeroClass_representable r ι Y z
  obtain ⟨y, rfl⟩ := Truncated.HomotopyCategory.mk_surjective y
  exact ⟨y, hy⟩

/-- 概要：元の wide 成分から元の三角圏 K₀ 余核への障害写像は全射。
方針：余核類を対象の K₀ 類で表し、その同じ頂点を wide へ持ち上げる。
規約：余核との単射性や零次 K 単射性はこの結論から推論しない。
使われ方：離散的障害の商群同定の全射側。 -/
theorem completionWideKZeroObstruction_surjective (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    Function.Surjective (completionWideKZeroObstruction r ι f) := by
  intro z
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective z
  obtain ⟨y, hy⟩ := completionKZeroVertex_surjective r ι Y a
  let F := ((multiSEndofunctor r).obj ι).map f
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F.val := stableModelHom_exact F
  let v : (LocalizingInvariants.completionCofiberWide F.val : SSet.{u}) _⦋0⦌ :=
    ⟨y, LocalizingInvariants.completionCofiberWide_vertex F.val
      (multiSEndofunctor_map_isIdempotentCompletion r ι f hf) y⟩
  refine ⟨SSet.π₀.mk v, ?_⟩
  exact congrArg (QuotientAddGroup.mk' (triangulatedKZeroSourceMap F).range) hy

end SerrePositivity.KST.SConstruction.Cofinality
