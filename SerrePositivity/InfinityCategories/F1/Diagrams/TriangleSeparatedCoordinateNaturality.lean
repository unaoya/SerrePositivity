module

public import SerrePositivity.InfinityCategories.F1.Diagrams.TriangleSeparatedMiddleCoordinates

/-!
概要：二切断・中間点・補助座標は、全ての面と退化を同時に保つ。
方針：path の像に対する有限座標の自然性を、元の K・L の単体の自然性へ接続する。
規約：K・L は任意。頂点に限定しない。
使われ方：全次数の再構成単体を一つの全族写像へ束ねる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma controlledTriangleCutMap_image {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (t : Fin (n + 1) →o Fin 2) (i j : Fin (m + 1)) (hi : t (α.toOrderHom i) = 0) :
    thickeningDirectHom.{u} α i j ≫ pathCutLastZeroMap t hi (α.toOrderHom j) =
      pathCutLastZeroMap (t.comp α.toOrderHom) hi j ≫ stdSimplex.map α := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro P
  apply stdSimplex.ext
  intro l
  exact pathCutLastZero_image α.toOrderHom t hi (P.obj l)

lemma controlledTriangleMiddleMap_image {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (t : Fin (n + 1) →o Fin 3) (i j : Fin (m + 1)) :
    thickeningDirectHom.{u} α i j ≫ trianglePathMiddleMap t (α.toOrderHom i) (α.toOrderHom j) =
      trianglePathMiddleMap (t.comp α.toOrderHom) i j := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro P
  apply stdSimplex.ext
  intro l
  exact trianglePathMiddle_image α.toOrderHom t (P.obj l)

lemma triangleSeparatedCoordinateMap_naturality
    {K L : SSet.{max u v}} {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (s : K _⦋n⦌) (r : L _⦋n⦌) (t : Fin (n + 1) →o Fin 3)
    (i j : Fin (m + 1)) (hi : t (α.toOrderHom i) = 0) :
    (SSet.uliftFunctor.{v, u}).map (thickeningDirectHom α i j) ≫
        triangleSeparatedCoordinateMap s r t hi (α.toOrderHom j) =
      triangleSeparatedCoordinateMap (K.map α.op s) (L.map α.op r)
        (t.comp α.toOrderHom) hi j := by
  have hz : (triangleZeroLabel t).comp α.toOrderHom =
      triangleZeroLabel (t.comp α.toOrderHom) := by ext i; rfl
  have hu : (triangleUpperLabel t).comp α.toOrderHom =
      triangleUpperLabel (t.comp α.toOrderHom) := by ext i; rfl
  apply CartesianMonoidalCategory.hom_ext
  · simp only [triangleSeparatedCoordinateMap, Category.assoc, lift_fst]
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun f => (SSet.uliftFunctor.{v, u}).map f ≫
        (HomotopyLimits.uliftStdSimplexIso.{u, v} 1).hom)
        (controlledTriangleMiddleMap_image α t i j)
  · apply CartesianMonoidalCategory.hom_ext
    · apply CartesianMonoidalCategory.hom_ext
      · simp only [triangleSeparatedCoordinateMap, Category.assoc, lift_fst, lift_snd]
        rw [triangleLiftedCoordinate_precomp, controlledTriangleCutMap_image,
          triangleLiftedCoordinate_naturality]
        rfl
      · simp only [triangleSeparatedCoordinateMap, Category.assoc, lift_snd, lift_fst]
        rw [triangleLiftedCoordinate_precomp, controlledTriangleCutMap_image,
          triangleLiftedCoordinate_naturality]
        rfl
    · simp only [triangleSeparatedCoordinateMap, Category.assoc, lift_snd]
      rw [triangleLiftedCoordinate_precomp, controlledTriangleCutMap_image,
        triangleLiftedCoordinate_naturality]
      rfl

end SerrePositivity.InfinityCategories
