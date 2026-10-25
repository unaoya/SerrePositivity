module
public import SerrePositivity.KST.SConstruction.DGKappaNativeBFFirstOmega

/-!
概要：元の前向き比較を保持した有限 native BF 再帰の段データ。
方針：同じ実 Kan 段・全 Hom 自然性・元正段との弱比較を一つの帰納データに保つ。
規約：未証明の Ω 条件は要求しない。使われ方：同じ四辺と全二胞体の同時再帰。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories NonConnective
open SimplicialModel
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：同じ元正段からの前向き弱比較を持つ実有限 BF 段。
方針：元の段と全入力自然性・Kan 性・弱比較を保持する。
規約：同じ未完備四角形の有限入力に限定。使われ方：正段の実帰納不変条件。 -/
structure DGKappaNativeBFFiniteStage (r : ℕ) where
  /-- 同じ全 Hom を保持する実段関手。 -/
  functor : EnrichedFunctor SSet.{max (u + 1) v} (DGKappaNativeBFFiniteInput.{u, v} R D I)
    PointedSSetObject.{max (u + 1) v}
  /-- 元の同じ境界商からの前向き比較。 -/
  comparison : ∀ C, (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I r).obj C ⟶ functor.obj C
  /-- 同じ比較の全高次入力自然性。 -/
  naturality : ∀ C E, (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I r).map C E ≫
      eHomWhiskerLeft SSet ((dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I r).obj C)
        (comparison E) =
    functor.map C E ≫ eHomWhiskerRight SSet (comparison C) (functor.obj E)
  /-- 同じ実段の Kan 性。 -/
  kan : ∀ C, KanComplex (functor.obj C).obj.right
  /-- 同じ前向き比較の anodyne 局所化可逆性。 -/
  weak : ∀ C, IsIso (AnodyneHomotopy.anodyneQ.map
    (show ((dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I r).obj C).obj ⟶
      (functor.obj C).obj from comparison C).right)

/-- 概要：同じ元の評価から作った最初の実段を帰納データに束ねる。
方針：構成済みの元の比較と全 Hom 自然性・Kan 性・anodyne 性を保持する。
規約：入力仮定の追加なし。使われ方：有限 BF 再帰の実基底。 -/
def dgKappaNativeBFFiniteInitialStage : DGKappaNativeBFFiniteStage.{u, v} R D I 0 where
  functor := dgKappaNativeBFFiniteFirstFunctor.{u, v} R D I
  comparison := dgKappaNativeBFFiniteFirstComparison.{u, v} R D I
  naturality := dgKappaNativeBFFiniteFirstComparison_whisker.{u, v} R D I
  kan C := dgKappaNativeBFFiniteFirst_kanComplex.{u, v} R D I C
  weak C := (Localization.inverts _ anodyneExtensions) _
    (dgKappaNativeBFFiniteFirstComparison_anodyne.{u, v} R D I C)

end SerrePositivity.KST.SConstruction
