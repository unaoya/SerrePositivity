module

public import SerrePositivity.InfinityCategories.F2.Presentable.FunctorColimitCreation
public import SerrePositivity.InfinityCategories.F2.Presentable.Definition
public import SerrePositivity.InfinityCategories.F2.Compact.UniverseColimits
public import SerrePositivity.InfinityCategories.F1.Compact.HomCovariantComparison

/-!
概要：関手圏の評価と compact 対象からの Hom の合成の filtered 保存を与える。
方針：元の余極限を e2 の点ごと計算へ移し、各点の compact 性を適用する。
規約：元の指定余錐と二宇宙の Hom 関手を保持する。
使われ方：P-12 の twisted arrow end 表示の各脚の κ-filtered 保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：小余極限が存在する標的の関手圏の評価は全小余極限を保つ。
方針：元の関手圏の余錐の点ごと計算を評価点に適用する。
規約：関手の始域の小ささを要求しない。使われ方：end の各評価脚の保存。 -/
lemma evaluateFunctorAt_preservesSmallColimits
    {A C : SSet.{u + 1}} [Quasicategory C] (hC : HasSmallColimits C)
    (a : A _⦋0⦌) : PreservesSmallColimits (evaluateFunctorAt (Y := C) a) := by
  intro J D c hc
  exact isPointwiseColimitCone_of_hasColimits (hC J) c hc a

/-- 概要：関手圏の評価は元の κ-filtered 余極限を保つ。
方針：評価の全小余極限保存を κ-filtered 保存へ制限する。
規約：元の κ は任意。使われ方：点ごとの compact Hom の合成。 -/
lemma evaluateFunctorAt_isKappaAccessibleFunctor
    {κ : Cardinal.{u}} {A C : SSet.{u + 1}} [Quasicategory C]
    (hC : HasSmallColimits C) (a : A _⦋0⦌) :
    IsKappaAccessibleFunctor κ (evaluateFunctorAt (Y := C) a) :=
  (evaluateFunctorAt_preservesSmallColimits hC a).isKappaAccessibleFunctor κ

/-- 概要：評価後の compact 対象からの Hom は元の κ-filtered 余極限を保つ。
方針：元の評価余錐に compact 性を適用し、持ち上げと後合成の厳密な式で戻す。
規約：小さい試験余錐の宇宙を拡大しない。
使われ方：Fun の写像空間の end 表示の各脚の保存。 -/
lemma preservesKappaFilteredColimits_compactHom_evaluation
    {κ : Cardinal.{u}} {A C : SSet.{u + 1}} [Quasicategory C]
    (hC : HasSmallColimits C) (a : A _⦋0⦌) (x : C _⦋0⦌)
    (hx : Compact.IsKappaCompact.{u, u + 1} κ x) :
    Compact.PreservesKappaFilteredColimits.{u, u + 1} κ
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (evaluateFunctorAt (Y := C) a) ≫
        covariantRepresentableInfinity x) := by
  intro I hI hFiltered D c hc
  have he := evaluateFunctorAt_preservesSmallColimits hC a I D c hc
  have h := hx I (D ≫ evaluateFunctorAt a) (mapJoinCocone (evaluateFunctorAt a) c) he
  apply (isColimitCone_iff_of_cocone_val_eq _ _ ?_).mpr h
  change (JoinCocone.ulift c).val ≫
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (evaluateFunctorAt a) ≫
        covariantRepresentableInfinity x) =
    (JoinCocone.ulift (mapJoinCocone (evaluateFunctorAt a) c)).val ≫
      covariantRepresentableInfinity x
  rw [← Category.assoc, ← Compact.ulift_mapJoinCocone_val]

/-- 概要：共同 Hom の始点固定制限も評価後に κ-filtered 余極限を保つ。
方針：共同 Hom と compact 性の定義に使う全共変 Hom の全自然同型を合成する。
規約：値ごとの同値では代用しない。使われ方：end の各脚の実際の係数関手。 -/
lemma preservesKappaFilteredColimits_jointHom_evaluation
    {κ : Cardinal.{u}} {A C : SSet.{u + 1}} [Quasicategory C]
    (hC : HasSmallColimits C) (a : A _⦋0⦌) (x : C _⦋0⦌)
    (hx : Compact.IsKappaCompact.{u, u + 1} κ x) :
    Compact.PreservesKappaFilteredColimits.{u, u + 1} κ
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (evaluateFunctorAt (Y := C) a) ≫
        homInfinityCovariant x) :=
  (preservesKappaFilteredColimits_compactHom_evaluation hC a x hx).of_functorIso
    ((Compact.homInfinityCovariant_covariantIso x).precomp
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (evaluateFunctorAt a))).symm

end SerrePositivity.InfinityCategories.F2.Presentable
