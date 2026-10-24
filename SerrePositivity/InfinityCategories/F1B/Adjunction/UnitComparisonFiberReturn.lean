module

public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitCommaSquareRecovery
public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitComparisonFiberPath
public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitCommaFiberComparison

/-!
概要：標準単位比較の指定導来 fiber から comma の区間写像空間へ戻る射。
方針：元の fiber の普遍ホモトピーを運んだ合成三角形と正方形の復元へ渡す。
規約：この射と順方向の比較の逆関係はまだ主張しない。
使われ方：局所存在判定の写像空間比較の逆向きの候補と、その標的射影の検証。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
variable {F : X ⟶ Y} {G : Y ⟶ X}

/-- 概要：指定導来 fiber の普遍ホモトピーから comma の写像空間へ戻る実際の射。
方針：普遍標的族と元の path 成分を正方形の復元へ渡す。
規約：比較射が同値であることや単位の普遍性は仮定しない。
使われ方：両合成のホモトピーを検証する逆向きの比較。 -/
noncomputable def unitComparisonFiberToCommaMapping
    (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) (w : (unitCommaFiber G x) _⦋0⦌) :
    unitCommaComparisonFiber η x w ⟶ intervalMappingSpace (unitCommaSectionVertex η x) w :=
  unitCommaMappingFamilyOfComparisonHomotopy η x w
    (unitComparisonFiberSource η x w) (unitComparisonFiberHomotopy η x w)

/-- 概要：戻る比較射の正方形表示は普遍標的族と普遍ホモトピーから復元した正方形。
方針：族と正方形の厳密な全単射の両逆を使う。
規約：coherence の代表の等式を保持する。
使われ方：戻る射の標的・四辺を回収する。 -/
lemma unitComparisonFiberToCommaMapping_square
    (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) (w : (unitCommaFiber G x) _⦋0⦌) :
    unitCommaFiberMappingSquare (unitComparisonFiberToCommaMapping η x w) =
      unitCommaSquareOfComparisonHomotopy η x w
        (unitComparisonFiberSource η x w) (unitComparisonFiberHomotopy η x w) :=
  unitCommaMappingFamilyOfComparisonHomotopy_square _ _ _ _ _

omit [Quasicategory Y] in
/-- 概要：comma の写像空間の族の標的の認識はパラメータ前合成に自然。
方針：展開の単射性と区間族・fiber 標的の前合成自然性を使う。
規約：パラメータの quasicategory 性は不要。
使われ方：戻る比較射の底の写像空間への射影。 -/
lemma unitCommaMappingTarget_precomp {A B : SSet.{u}}
    (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) (w : (unitCommaFiber G x) _⦋0⦌)
    (i : A ⟶ B) (f : B ⟶ intervalMappingSpace (unitCommaSectionVertex η x) w) :
    unitCommaSquareTargetFamily η x w (unitCommaFiberMappingSquare (i ≫ f)) =
      i ≫ unitCommaSquareTargetFamily η x w (unitCommaFiberMappingSquare f) := by
  apply intervalMappingUncurry_injective
  rw [unitCommaSquareTargetFamily_uncurry, intervalMappingUncurry_precomp,
    unitCommaSquareTargetFamily_uncurry]
  change unitCommaFiberTarget (intervalMappingUncurry (i ≫ f)) =
    (Δ[1] : SSet.{u}) ◁ i ≫ unitCommaFiberTarget (intervalMappingUncurry f)
  rw [intervalMappingUncurry_precomp, unitCommaFiberTarget_precomp]

/-- 概要：戻る比較射は元の導来 fiber の始域座標を厳密に保持する。
方針：標的のパラメータ自然性と復元した正方形の標的の回収を使う。
規約：射影の等式であり、比較の逆関係はまだ主張しない。
使われ方：二つの比較射が同じ底の写像空間上にあることの確認。 -/
lemma unitComparisonFiberToCommaMapping_projection
    (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) (w : (unitCommaFiber G x) _⦋0⦌) :
    unitComparisonFiberToCommaMapping η x w ≫
      unitCommaSquareTargetFamily η x w
        (unitCommaFiberMappingSquare (𝟙 (intervalMappingSpace (unitCommaSectionVertex η x) w))) =
      unitComparisonFiberSource η x w := by
  have h := unitCommaMappingTarget_precomp η x w
    (unitComparisonFiberToCommaMapping η x w)
    (𝟙 (intervalMappingSpace (unitCommaSectionVertex η x) w))
  rw [Category.comp_id] at h
  rw [← h, unitComparisonFiberToCommaMapping_square,
    unitCommaSquareOfComparisonHomotopy_target]

/-- 概要：導来 fiber の普遍ホモトピーを path 表示へ戻すと元の path 成分。
方針：包含で検査し、区間交換・curry の両逆と path の普遍ホモトピーの定義を使う。
規約：正規化した端点だけでなく path 自体の厳密な等式。
使われ方：戻る比較の入力が元の導来 fiber の coherence を保持することの確認。 -/
lemma unitComparisonFiberHomotopy_path
    (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) (w : (unitCommaFiber G x) _⦋0⦌) :
    homotopyEquivalencePath (unitComparisonFiberHomotopy η x w) =
      unitComparisonFiberPath η x w := by
  let B := intervalMappingSpace x (G.app (Opposite.op ⦋0⦌) (unitCommaFiberTargetVertex G x w))
  let P := unitCommaComparisonFiber η x w
  let π := unitComparisonFiberPath η x w
  have : Mono (equivalencePathι B) := by unfold equivalencePathι; infer_instance
  apply (cancel_mono (equivalencePathι B)).mp
  rw [show homotopyEquivalencePath (unitComparisonFiberHomotopy η x w) ≫ equivalencePathι B =
    curry ((β_ (Δ[1] : SSet.{u}) P).hom ≫ (unitComparisonFiberHomotopy η x w).h)
      from fullSubcomplexLift_ι _ _ _]
  apply uncurry_injective
  rw [uncurry_curry, uncurry_natural_left]
  change (β_ (Δ[1] : SSet.{u}) P).hom ≫
    ((π ▷ (Δ[1] : SSet.{u})) ≫ ((β_ (equivalencePath B) (Δ[1] : SSet.{u})).hom ≫
      uncurry (equivalencePathι B))) = (Δ[1] : SSet.{u}) ◁ π ≫ uncurry (equivalencePathι B)
  have hb : (β_ (Δ[1] : SSet.{u}) P).hom ≫ (π ▷ (Δ[1] : SSet.{u})) =
      (Δ[1] : SSet.{u}) ◁ π ≫ (β_ (Δ[1] : SSet.{u}) (equivalencePath B)).hom := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  rw [← Category.assoc, hb]
  simp only [Category.assoc, reassoc_of% SymmetricCategory.symmetry]

end SerrePositivity.InfinityCategories
