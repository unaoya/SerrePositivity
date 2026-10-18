module
public import SerrePositivity.KST.SConstruction.SuspensionAssembly
public import SerrePositivity.KST.SConstruction.CofiberProjectionNaturality

/-! # suspension の反復 S の組み立ての自然性
概要：L9 の suspension を源とする反復間の比較射は、安定な入力の射について自然。
方針：商射影の tensor のエピ性で検出し、元の cylinder の自然性へ戻す。
規約：源は一次方向を固定した境界商。使われ方：スペクトルの構造写像の比較図式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial

/-- 概要：suspension への二つの商射影の tensor はエピ。
方針：一般の cofiber の tensor 射影のエピ性。
規約：各入力・各反復数。使われ方：構造射の等号の検出。 -/
instance oneDirectionSuspensionProjection_epi (r : ℕ) (X : StableModel.{u}) :
    Epi (oneDirectionSuspensionProjection r X) :=
  cofiberTensorProjection_epi (boundary.{u} 1).ι (oneDirectionFatBoundary (r + 1) X).ι

/-- 概要：一次方向の境界商への自由な基点の射影は入力について自然。
方針：底の商射影の自然性を基点追加の Hom 同値で移す。
規約：厳密な点つき等号。使われ方：suspension 射影の自然性。 -/
lemma oneDirectionCofiberProjection_naturality (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    PointedObject.adjoinFunctor.map ((oneDirectionRealizationFunctor (r + 1)).map f) ≫
        PointedObject.cofiberProjection (oneDirectionFatBoundary (r + 1) Y).ι =
      PointedObject.cofiberProjection (oneDirectionFatBoundary (r + 1) X).ι ≫
        oneDirectionReducedRealizationMap r f :=
  cofiberProjection_naturality_of_quotient (oneDirectionFatBoundary (r + 1) X).ι
    (oneDirectionFatBoundary (r + 1) Y).ι ((oneDirectionRealizationFunctor (r + 1)).map f)
    (oneDirectionReducedRealizationMap r f) (oneDirectionReducedRealizationMap_quotient r f)

/-- 概要：suspension への二つの商射影は入力について自然。
方針：tensor の合成則と境界商の射影の自然性を使う。
規約：円の因子は固定する。使われ方：suspension の組み立ての自然性の検証。 -/
lemma oneDirectionSuspensionProjection_naturality (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    (PointedObject.adjoin (Δ[1] : SSet.{u}) ◁
        PointedObject.adjoinFunctor.map ((oneDirectionRealizationFunctor (r + 1)).map f)) ≫
        oneDirectionSuspensionProjection r Y =
      oneDirectionSuspensionProjection r X ≫
        (PointedSimplicialSet.circle.{u} ◁ oneDirectionReducedRealizationMap r f) := by
  change (𝟙 (PointedObject.adjoin (Δ[1] : SSet.{u})) ⊗ₘ
      PointedObject.adjoinFunctor.map ((oneDirectionRealizationFunctor (r + 1)).map f)) ≫
      (PointedObject.cofiberProjection (boundary.{u} 1).ι ⊗ₘ
        PointedObject.cofiberProjection (oneDirectionFatBoundary (r + 1) Y).ι) =
    (PointedObject.cofiberProjection (boundary.{u} 1).ι ⊗ₘ
      PointedObject.cofiberProjection (oneDirectionFatBoundary (r + 1) X).ι) ≫
      (𝟙 PointedSimplicialSet.circle.{u} ⊗ₘ oneDirectionReducedRealizationMap r f)
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  simp only [Category.id_comp, oneDirectionCofiberProjection_naturality]
  have hc : PointedObject.cofiberProjection (boundary.{u} 1).ι ≫
      𝟙 PointedSimplicialSet.circle.{u} = PointedObject.cofiberProjection (boundary.{u} 1).ι :=
    Category.comp_id _
  rw [hc]

/-- 概要：suspension から次の反復の境界商への組み立ては入力について自然。
方針：二つの商射影で検出し、cylinder の自然性と各商の回収式を使う。
規約：全 cofiber 保存射を含む。使われ方：構造写像の自然変換。 -/
lemma oneDirectionSuspensionAssembly_naturality (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    (PointedSimplicialSet.circle.{u} ◁ oneDirectionReducedRealizationMap r f) ≫
        oneDirectionSuspensionAssembly r Y =
      oneDirectionSuspensionAssembly r X ≫ boundaryReducedRealizationMap (r + 1) f := by
  apply (cancel_epi (oneDirectionSuspensionProjection r X)).1
  rw [← Category.assoc, ← oneDirectionSuspensionProjection_naturality, Category.assoc,
    oneDirectionSuspensionAssembly_quotient, ← Category.assoc,
    oneDirectionSuspensionAssembly_quotient]
  have hp := adjoinTensorMap_precomp (𝟙 (Δ[1] : SSet.{u}))
    ((oneDirectionRealizationFunctor (r + 1)).map f) (boundaryReducedRealization (r + 1) Y)
    (multiDiagonalAssembly (r + 1) Y ≫ boundaryReductionQuotient (r + 1) Y)
  simp only [CategoryTheory.Functor.map_id, id_tensorHom] at hp
  change (PointedObject.adjoin (Δ[1] : SSet.{u}) ◁
      PointedObject.adjoinFunctor.map ((oneDirectionRealizationFunctor (r + 1)).map f)) ≫
      adjoinTensorMap (boundaryReducedRealization (r + 1) Y)
        (multiDiagonalAssembly (r + 1) Y ≫ boundaryReductionQuotient (r + 1) Y) =
    adjoinTensorMap (boundaryReducedRealization (r + 1) Y)
      (((Δ[1] : SSet.{u}) ◁ (oneDirectionRealizationFunctor (r + 1)).map f) ≫
        multiDiagonalAssembly (r + 1) Y ≫ boundaryReductionQuotient (r + 1) Y) at hp
  rw [hp, adjoinTensorMap_postcomp]
  congr 1
  rw [← Category.assoc, multiDiagonalAssembly_naturality, Category.assoc,
    ← boundaryReducedRealizationMap_quotient, ← Category.assoc]

/-- 概要：suspension の組み立てを入力についての自然変換にまとめる。
方針：各成分を構成済みの suspension の射とする。
規約：源は一次方向の境界商の suspension。使われ方：反復間の構造写像の比較図式。 -/
def oneDirectionSuspensionAssemblyNat (r : ℕ) :
    oneDirectionReducedRealizationFunctor r ⋙ tensorLeft PointedSimplicialSet.circle.{u} ⟶
      boundaryReducedRealizationFunctor (r + 1) where
  app := oneDirectionSuspensionAssembly r
  naturality {_X _Y} f := oneDirectionSuspensionAssembly_naturality r f

end SerrePositivity.KST.SConstruction
