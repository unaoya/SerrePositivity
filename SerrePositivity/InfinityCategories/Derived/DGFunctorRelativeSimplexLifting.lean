module
public import SerrePositivity.InfinityCategories.Derived.DGSimplexFaceExtensionality
public import SerrePositivity.InfinityCategories.Derived.DGFunctorRelativeTopLifting
public import SerrePositivity.InfinityCategories.Derived.DGBoundaryTopCompletion
public import SerrePositivity.InfinityCategories.DGNerve.Functor

/-! # 全射 Hom 準同型な dg 関手に沿う相対単体の持ち上げ

概要：全ての面が指定された持ち上げに一致する目標単体を、面を保って持ち上げる。
方針：面から対象族と最上位の右辺を同定し、最上位だけを同時持ち上げで置換する。
規約：全正次元を扱う。使われ方：β3 の dg nerve の自明 Kan fibration。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable {A : Type u} [CommRing A] {D : Type v} {E : Type w}
variable [DGCategory A D] [DGCategory A E]

/-- 面を保った正次元の dg 単体の相対持ち上げ。 -/
lemma dgFunctor_relative_simplex_lift (F : DGFunctor A D E)
    (hs : ∀ x y (i : ℤ), Function.Surjective ((F.map x y).f i))
    (hq : HomQuasiIso F) {n : ℕ} (s : SimplexData A D (n + 1))
    (he : ∀ I, I ≠ Finset.univ → s.Equation I) (t : Simplex A E (n + 1))
    (hfaces : ∀ j : Fin (n + 2), (s.map F).pullback j.succAboveOrderEmb.toOrderHom =
      t.toSimplexData.pullback j.succAboveOrderEmb.toOrderHom) :
    ∃ u : Simplex A D (n + 1),
      (∀ j : Fin (n + 2), u.toSimplexData.pullback j.succAboveOrderEmb.toOrderHom =
        s.pullback j.succAboveOrderEmb.toOrderHom) ∧ u.map F = t := by
  have hobj := SimplexData.obj_eq_of_selected_faces Finset.univ
    (SimplexData.allFacesCoverVertices n) (s.map F) t.toSimplexData (fun j _ => hfaces j)
  rcases t with ⟨⟨o, f⟩, ht⟩
  change (fun i => F.obj (s.obj i)) = o at hobj
  subst o
  let t' : Simplex A E (n + 1) := ⟨⟨fun i => F.obj (s.obj i), f⟩, ht⟩
  let U : Finset (Fin (n + 2)) := Finset.univ
  have hU : 2 ≤ U.card := by simp [U]
  let a := U.min' (Index.nonempty hU)
  let b := U.max' (Index.nonempty hU)
  let k : ℤ := 2 - (U.card : ℤ)
  let r := t'.hom U a b k hU rfl rfl rfl
  have hr : (F.map (s.obj a) (s.obj b)).f (k + 1)
      (s.rhs Finset.univ a b k hU rfl rfl rfl) = differential A r := by
    rw [SimplexData.map_rhs]
    exact (eq_of_heq (SimplexData.rhs_heq_of_all_faces (s.map F) t'.toSimplexData
      hfaces a b k hU rfl rfl rfl)).trans (t'.equation U a b k hU rfl rfl rfl).symm
  obtain ⟨q, dq, hq'⟩ := dgFunctor_relative_top_lift F hs hq s he a b k hU rfl rfl rfl r hr
  let u := dgCompleteTopSimplex s he a b k hU rfl rfl rfl q dq
  refine ⟨u, fun j => dgCompleteTopSimplex_pullback_face s he a b k hU rfl rfl rfl q dq j, ?_⟩
  change u.map F = t'
  apply Simplex.ext
  apply SimplexData.ext_of_all_faces_and_top
  · intro j
    change (u.toSimplexData.map F).pullback j.succAboveOrderEmb.toOrderHom =
      t'.toSimplexData.pullback j.succAboveOrderEmb.toOrderHom
    rw [← SimplexData.map_pullback,
      dgCompleteTopSimplex_pullback_face s he a b k hU rfl rfl rfl q dq,
      SimplexData.map_pullback]
    exact hfaces j
  · intro c d l hI hc hd hl
    have hca : c = a := hc
    have hdb : d = b := hd
    have hlk : l = k := hl
    cases hca
    cases hdb
    cases hlk
    apply heq_of_eq
    change (F.map (s.obj a) (s.obj b)).f k
      ((s.replaceFixed U a b k hU rfl rfl rfl q).hom U a b k hU rfl rfl rfl) = r
    rw [SimplexData.replaceFixed_hom_same]
    exact hq'

end SerrePositivity.InfinityCategories
