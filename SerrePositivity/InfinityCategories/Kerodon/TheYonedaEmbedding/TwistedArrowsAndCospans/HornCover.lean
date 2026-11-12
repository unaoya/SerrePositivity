module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.HalfCompatibility
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.HornFaceCompatibility
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.WeightCover
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RangeCoverGluing

/-!
概要：twisted arrow のホーンの各面と左右の半分を、一つの被覆の図式へ束ねる。
方針：二重の Option で二つの半分と面を区別し、全ての共通部分で既証明の一致を使う。
規約：像の和は元の join の重みの延長領域そのものである。
使われ方：inner anodyne な固定領域上の図式から実際のホーン充填を得る。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- none は左半分、some none は右半分、残りはホーンの面。 -/
def twistedArrowHornCoverSource (n : ℕ) (i : Fin (n + 2)) :
    Option (Option {j : Fin (n + 2) // j ≠ i}) → SSet.{u}
  | none => (Δ[n + 1] : SSet.{u}).op
  | some none => Δ[n + 1]
  | some (some _) => _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj ⦋n⦌

/-- 左右の半分とホーンの面から全重みへの被覆射。 -/
def twistedArrowHornCoverMap (n : ℕ) (i : Fin (n + 2)) :
    ∀ u, twistedArrowHornCoverSource.{u} n i u ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj ⦋n + 1⦌
  | none => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n + 1] : SSet.{u}).op Δ[n + 1]
  | some none => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n + 1] : SSet.{u}).op Δ[n + 1]
  | some (some j) => _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ j.val)

/-- 被覆上の図式は、左右では底の成分、各面では元のホーンの単体。 -/
def twistedArrowHornCoverDiagram {C : SSet.{u}} {n : ℕ} {i : Fin (n + 2)}
    (a : (Λ[n + 1, i] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow C)
    (b : (Δ[n + 1] : SSet.{u}) ⟶ C.op ⊗ C) :
    ∀ u, twistedArrowHornCoverSource n i u ⟶ C
  | none => SSet.opFunctor.map (b ≫ fst C.op C) ≫
      (SSet.opFunctorCompOpFunctorIso.app C).hom
  | some none => b ≫ snd C.op C
  | some (some j) => SSet.yonedaEquiv (horn.ι i j.val j.property ≫ a)

/-- 被覆上の指定図式は、任意の像の共通部分で一致する。 -/
lemma twistedArrowHornCover_compatible {C : SSet.{u}} {n : ℕ} {i : Fin (n + 2)}
    (a : (Λ[n + 1, i] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow C)
    (b : (Δ[n + 1] : SSet.{u}) ⟶ C.op ⊗ C)
    (sq : CommSq a Λ[n + 1, i].ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) b)
    (u v : Option (Option {j : Fin (n + 2) // j ≠ i})) (d : SimplexCategoryᵒᵖ)
    (x : (twistedArrowHornCoverSource n i u).obj d)
    (y : (twistedArrowHornCoverSource n i v).obj d)
    (hxy : (twistedArrowHornCoverMap n i u).app d x =
      (twistedArrowHornCoverMap n i v).app d y) :
    (twistedArrowHornCoverDiagram a b u).app d x =
      (twistedArrowHornCoverDiagram a b v).app d y := by
  cases u with
  | none =>
    cases v with
    | none =>
      have he : x = y := (mono_iff_injective
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n + 1] : SSet.{u}).op Δ[n + 1]).app d)).mp inferInstance hxy
      subst y
      rfl
    | some v =>
      cases v with
      | none => exact False.elim (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.joinInl_app_ne_joinInr d x y hxy)
      | some j =>
        exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHornFace_left_compatible a b sq j.val j.property d y x hxy.symm).symm
  | some u =>
    cases u with
    | none =>
      cases v with
      | none => exact False.elim (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.joinInl_app_ne_joinInr d y x hxy.symm)
      | some v =>
        cases v with
        | none =>
          have he : x = y := (mono_iff_injective
            ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n + 1] : SSet.{u}).op Δ[n + 1]).app d)).mp inferInstance hxy
          subst y
          rfl
        | some j =>
          exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHornFace_right_compatible a b sq j.val j.property d y x hxy.symm).symm
    | some j =>
      cases v with
      | none => exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHornFace_left_compatible a b sq j.val j.property d x y hxy
      | some v =>
        cases v with
        | none => exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHornFace_right_compatible a b sq j.val j.property d x y hxy
        | some k => exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseHornFaces_compatible a j.val k.val j.property k.property d x y hxy

/-- 被覆射の像の和は、inner anodyne な元の固定領域。 -/
lemma twistedArrowHornCover_range_eq {n : ℕ} (i : Fin (n + 2)) :
    (⨆ u, Subcomplex.range (twistedArrowHornCoverMap.{u} n i u)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowWeightDomain (n + 1) i := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowWeightDomain_eq_face_cover]
  apply le_antisymm
  · apply iSup_le
    intro u
    cases u with
    | none => exact le_sup_left
    | some u =>
      cases u with
      | none => exact le_trans le_sup_left le_sup_right
      | some j =>
        exact le_trans (le_trans
          (le_iSup (fun k : {j : Fin (n + 2) // j ≠ i} ↦
            Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ k.val))) j)
          le_sup_right) le_sup_right
  · refine sup_le (le_iSup (fun u ↦ Subcomplex.range (twistedArrowHornCoverMap n i u)) none) ?_
    refine sup_le (le_iSup (fun u ↦ Subcomplex.range (twistedArrowHornCoverMap n i u))
      (some none)) ?_
    exact iSup_le (fun j ↦ le_iSup
      (fun u ↦ Subcomplex.range (twistedArrowHornCoverMap n i u)) (some (some j)))

/-- 全ての指定データは、被覆の像の和上に厳密に接合できる。 -/
lemma exists_twistedArrowHornCover_gluing {C : SSet.{u}} {n : ℕ} {i : Fin (n + 2)}
    (a : (Λ[n + 1, i] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow C)
    (b : (Δ[n + 1] : SSet.{u}) ⟶ C.op ⊗ C)
    (sq : CommSq a Λ[n + 1, i].ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) b) :
    ∃ F : ((⨆ u, Subcomplex.range (twistedArrowHornCoverMap n i u) :
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj ⦋n + 1⦌).Subcomplex) : SSet.{u}) ⟶ C,
      ∀ u, Subcomplex.lift (twistedArrowHornCoverMap n i u)
        (le_iSup (fun v ↦ Subcomplex.range (twistedArrowHornCoverMap n i v)) u) ≫ F =
          twistedArrowHornCoverDiagram a b u :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.exists_map_of_compatible_range_cover (twistedArrowHornCoverSource n i)
    (twistedArrowHornCoverMap n i) (twistedArrowHornCoverDiagram a b)
    (twistedArrowHornCover_compatible a b sq)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
