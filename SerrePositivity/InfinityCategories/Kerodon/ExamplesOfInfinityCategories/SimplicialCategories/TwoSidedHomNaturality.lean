module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.TwoSidedHomSimplex
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathCutStageReindex

/-!
概要：左右を補間する coherent 単体を、区間二つと全 Hom を保つ単体集合の射へ束ねる。
方針：元の thickening の添字写像を path の像に照合し、各ラベルで Hom を正規化する。
規約：局所 Kan 性を使わず、全ての面と退化を同時に扱う。
使われ方：native な左 Hom 区間と反転作用の右 Hom 区間の比較。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 単体圏の元の添字写像が、同じ二端点の豊穣 Hom に誘導する射。 -/
def thickeningDirectHom {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) (i j : Fin (m + 1)) :
    SimplicialCategory.sHom
      (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (m + 1)))) ⟨ULift.up j⟩ ⟶
    SimplicialCategory.sHom
      (⟨ULift.up (α.toOrderHom i)⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))
      ⟨ULift.up (α.toOrderHom j)⟩ :=
  (SimplicialThickening.functor α.toOrderHom.uliftMap).map _ _

/-- thickening の元の射は、混合 Hom の段階ごとの評価と厳密に可換。 -/
lemma thickeningDirectHom_pathCutStageMap {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (t s : Fin (n + 1) →o Fin 2) (i j : Fin (m + 1))
    (hi : t (α.toOrderHom i) = 0) (hj : t (α.toOrderHom j) = 1)
    {H : SSet.{u}} (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision H) _⦋n⦌) :
    thickeningDirectHom α i j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutEdgewiseStageMap t s hi hj σ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutEdgewiseStageMap (t.comp α.toOrderHom) (s.comp α.toOrderHom) hi hj
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision H).map α.op σ) := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutEdgewiseStageMap_image α t s i j hi hj σ

/-- 混合 Hom の作用は、面・退化による添字変換を全高次で保つ。 -/
lemma coherentTwoSidedHom_naturality {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (SimplicialCategory.sHom X Y)) _⦋n⦌)
    (t s : Fin (n + 1) →o Fin 2) (i j : Fin (m + 1)) :
    thickeningDirectHom α i j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTwoSidedHom σ t s
      (α.toOrderHom i) (α.toOrderHom j) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTwoSidedHom ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (SimplicialCategory.sHom X Y)).map α.op σ)
      (t.comp α.toOrderHom) (s.comp α.toOrderHom) i j := by
  let σ' := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (SimplicialCategory.sHom X Y)).map α.op σ
  let t' := t.comp α.toOrderHom
  let s' := s.comp α.toOrderHom
  by_cases hi : t (α.toOrderHom i) = 0 <;> by_cases hj : t (α.toOrderHom j) = 0
  · apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTwoSidedHomObj_zero X Y t' i hi)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTwoSidedHomObj_zero X Y t' j hj)))).1
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTwoSidedHom_zero_zero σ t s _ _ hi hj,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTwoSidedHom_zero_zero σ' t' s' i j hi hj, comp_toUnit_assoc]
  · apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTwoSidedHomObj_zero X Y t' i hi)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTwoSidedHomObj_one X Y t' j hj)))).1
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTwoSidedHom_zero_one σ t s _ _ hi hj,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTwoSidedHom_zero_one σ' t' s' i j hi hj]
    exact thickeningDirectHom_pathCutStageMap α t s i j hi (by omega) σ
  · apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    exact False.elim (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutSameSimplex_backward_false t' hi hj (P.obj 0))
  · apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTwoSidedHomObj_one X Y t' i hi)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTwoSidedHomObj_one X Y t' j hj)))).1
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTwoSidedHom_one_one σ t s _ _ hi hj,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTwoSidedHom_one_one σ' t' s' i j hi hj, comp_toUnit_assoc]

/-- 同じ coherent 単体の構成は、任意の面・退化と同時に可換。 -/
lemma coherentTwoSidedHomSimplex_naturality {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (SimplicialCategory.sHom X Y)) _⦋n⦌)
    (t s : Fin (n + 1) →o Fin 2) :
    (SimplicialNerve C).map α.op (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTwoSidedHomSimplex σ t s) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTwoSidedHomSimplex
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (SimplicialCategory.sHom X Y)).map α.op σ)
        (t.comp α.toOrderHom) (s.comp α.toOrderHom) := by
  apply EnrichedFunctor.ext SSet
    (F := (SimplicialNerve C).map α.op (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTwoSidedHomSimplex σ t s))
    (G := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTwoSidedHomSimplex
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (SimplicialCategory.sHom X Y)).map α.op σ)
      (t.comp α.toOrderHom) (s.comp α.toOrderHom)) (fun _ => rfl)
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  change (thickeningDirectHom α i j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTwoSidedHom σ t s
    (α.toOrderHom i) (α.toOrderHom j)) ≫ eqToHom _ = _
  rw [eqToHom_refl, Category.comp_id]
  exact coherentTwoSidedHom_naturality α σ t s i j

/-- 全 Hom の共通解像と二つの区間を保持した、左右を補間する coherent な族。 -/
def coherentTwoSidedHomFamily {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Y : C) :
    ((Δ[1] : SSet.{max u v}) ⊗ Δ[1]) ⊗ (SSet.uliftFunctor.{v, u}).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (SimplicialCategory.sHom X Y)) ⟶ SimplicialNerve C where
  app _ := ↾fun ⟨⟨t, s⟩, σ⟩ => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTwoSidedHomSimplex σ.down
    (stdSimplex.objEquiv t).toOrderHom (stdSimplex.objEquiv s).toOrderHom
  naturality := by
    rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ α
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨t, s⟩, σ⟩
    exact (coherentTwoSidedHomSimplex_naturality α.unop σ.down
      (stdSimplex.objEquiv t).toOrderHom (stdSimplex.objEquiv s).toOrderHom).symm

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
