module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeInitialFixed
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.CosliceFiberCoordinates
public import SerrePositivity.InfinityCategories.F1.Coherent.Vertices

/-!
概要：coherent nerve の coslice の単体を、初点の対象を固定した simplex として読む。
方針：点と標準単体の join の同型で移し、固定条件と全添字変換を追跡する。
規約：終点の fiber には制限せず、coslice 全体を扱う。
使われ方：任意の coherent な錐全体上での豊穣 Hom の前合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- coslice の n 単体を、元の coherent nerve の (n+1) 単体へ戻す。 -/
def coherentCosliceSourceSimplex (z : C) {n : ℕ}
    (s : (sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex z))) _⦋n⦌) :
    (SimplicialNerve C) _⦋n + 1⦌ :=
  SSet.yonedaEquiv ((leftPointStdSimplexIso n).inv ≫ s.val)

/-- coslice の固定条件は、読み戻した simplex の初点を z に固定する。 -/
lemma coherentCosliceSourceSimplex_apex (z : C) {n : ℕ}
    (s : (sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex z))) _⦋n⦌) :
    (SimplicialNerve C).map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op
      (coherentCosliceSourceSimplex z s) = coherentNerveVertex z := by
  change (SimplicialNerve C).map _ (SSet.yonedaEquiv _) = _
  rw [SSet.yonedaEquiv_naturality, ← Category.assoc, leftPointStdSimplexIso_first_inv,
    s.property, Equiv.apply_symm_apply]

/-- coslice から読み戻した simplex の tail は実際の射影の単体。 -/
lemma coherentCosliceSourceSimplex_tail (z : C) {n : ℕ}
    (s : (sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex z))) _⦋n⦌) :
    (SimplicialNerve C).δ 0 (coherentCosliceSourceSimplex z s) =
      (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex z))).app
        (Opposite.op ⦋n⦌) s := by
  change (SimplicialNerve C).map _ (SSet.yonedaEquiv _) = _
  rw [SSet.yonedaEquiv_naturality, ← Category.assoc]
  erw [leftPointStdSimplexIso_face_inv]
  rfl

/-- coslice の面・退化は初点固定の coherent simplex の制限に一致する。 -/
lemma coherentCosliceSourceSimplex_reindex (z : C) {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (s : (sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex z))) _⦋n⦌) :
    (SimplicialThickening.functor (prependOrderHom α.toOrderHom).uliftMap).comp SSet
        (coherentCosliceSourceSimplex z s) =
      coherentCosliceSourceSimplex z
        ((sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex z))).map α.op s) := by
  have hi : stdSimplex.map (SimplexCategory.mkHom (prependOrderHom α.toOrderHom)) ≫
      (leftPointStdSimplexIso.{max u v} n).inv =
        (leftPointStdSimplexIso m).inv ≫ joinMap (𝟙 Δ[0]) (stdSimplex.map α) := by
    apply (cancel_mono (leftPointStdSimplexIso n).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    erw [joinStdSimplexIso_point_naturality α]
    erw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  change (SimplicialNerve C).map
      (SimplexCategory.mkHom (prependOrderHom α.toOrderHom)).op (SSet.yonedaEquiv _) = _
  rw [SSet.yonedaEquiv_naturality, ← Category.assoc, hi]
  rfl

/-- coslice の単体を、初点の対象の等式も保持する座標にまとめる。 -/
def cosliceInitialCoordinates (z : C) {n : ℕ}
    (s : (sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex z))) _⦋n⦌) :
    fixedInitialSimplex z n :=
  ⟨coherentCosliceSourceSimplex z s,
    congrArg (fun T : (SimplicialNerve C) _⦋0⦌ ↦ T.obj ⟨ULift.up 0⟩)
      (coherentCosliceSourceSimplex_apex z s)⟩

/-- 初点固定の座標への変換も全ての面・退化と厳密に可換。 -/
lemma cosliceInitialCoordinates_reindex (z : C) {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (s : (sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex z))) _⦋n⦌) :
    cosliceInitialCoordinates z
        ((sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex z))).map α.op s) =
      fixedInitialSimplexReindex z α (cosliceInitialCoordinates z s) := by
  apply Subtype.ext
  exact (coherentCosliceSourceSimplex_reindex z α s).symm

end
end SerrePositivity.InfinityCategories.HomotopyLimits
