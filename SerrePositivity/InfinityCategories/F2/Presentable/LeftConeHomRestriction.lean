module

public import SerrePositivity.InfinityCategories.F2.Presentable.ConeApexHomRestriction
public import SerrePositivity.InfinityCategories.F2.Presentable.FunctorHomWhiskering
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorOppositeHom
public import SerrePositivity.InfinityCategories.Core.ConeOpposite
public import SerrePositivity.InfinityCategories.Core.JoinTensorPoint

/-!
概要：定値図式から元の全錐への Hom は、左頂点への制限で決まる。
方針：反転 Hom と join の反転同型で、余錐の右頂点の全単射へ移す。
規約：元の前合成写像そのものの全単射性を結論する。
使われ方：普遍錐の余単位と随伴の Hom 対応の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：前合成の Hom 全単射は、全図式を反転して判定できる。
方針：反転 Hom の全単射と前合成の可換な比較を使う。
規約：始域の quasicategory 性を要求しない。
使われ方：錐の左頂点の Hom 判定を余錐へ移す。 -/
lemma functorHomPrecomp_bijective_of_opposite {A B X : SSet.{u}} [Quasicategory X]
    (i : A ⟶ B) (F G : B ⟶ X)
    (h : Function.Bijective
      ((hoFunctor.map ((pre (SSet.opFunctor.map i)).app X.op)).toFunctor.map :
        FunctorHom (SSet.opFunctor.map G) (SSet.opFunctor.map F) → _)) :
    Function.Bijective ((hoFunctor.map ((pre i).app X)).toFunctor.map :
      FunctorHom F G → _) := by
  let e := F1B.functorOppositeHomEquiv (i ≫ F) (i ≫ G)
  have hb := h.comp (F1B.functorOppositeHomEquiv F G).bijective
  have heq :
      ((hoFunctor.map ((pre (SSet.opFunctor.map i)).app X.op)).toFunctor.map) ∘
        F1B.functorOppositeHomEquiv F G =
      e ∘ ((hoFunctor.map ((pre i).app X)).toFunctor.map) := by
    funext α
    exact (F1B.functorOppositeHomEquiv_precomp i α).symm
  rw [heq] at hb
  exact hb.of_comp_left e.injective

/-- 概要：定値始域から元の全錐への Hom は左頂点への制限で全単射。
方針：join を反転し、左右の包含の交換と右頂点の全単射を合成する。
規約：標的 X のみ quasicategory とする。
使われ方：指定した極限錐の余単位の普遍性。 -/
lemma leftConeApex_homRestriction_bijective {K X : SSet.{u}} [Quasicategory X]
    (H : join (Δ[0] : SSet.{u}) K ⟶ X) (y : X _⦋0⦌) :
    Function.Bijective
      ((hoFunctor.map ((pre (joinInl (Δ[0] : SSet.{u}) K)).app X)).toFunctor.map :
        FunctorHom (SSet.const y) H → _) := by
  apply functorHomPrecomp_bijective_of_opposite
  let t := (stdSimplex.opIso ⦋0⦌).inv
  let j := joinMap (𝟙 K.op) t ≫ (stableJoinReverseIso (Δ[0] : SSet.{u}) K).inv
  have hj : IsIso j := by dsimp [j, t]; infer_instance
  have hjf := ((isPrecompositionEquivalence_of_iso (asIso j)) X.op).isFullyFaithful
  have ht : IsIso t := by dsimp [t]; infer_instance
  have htf := ((isPrecompositionEquivalence_of_iso (asIso t)) X.op).isFullyFaithful
  have hs : joinInr K.op (Δ[0] : SSet.{u}) ≫ j =
      t ≫ SSet.opFunctor.map (joinInl (Δ[0] : SSet.{u}) K) := by
    dsimp [j]
    rw [← Category.assoc, joinInr_joinMap, Category.assoc, stableJoinReverse_inr_inv]
  have hc : SSet.opFunctor.map (SSet.const y : join (Δ[0] : SSet.{u}) K ⟶ X) =
      SSet.const (SSet.opObjEquiv.symm y) := by rfl
  rw [hc]
  have hr := coneApex_homRestriction_bijective
    (j ≫ SSet.opFunctor.map H) (SSet.opObjEquiv.symm y)
  have hp := hjf.homotopyCategoryMap_bijective
    (functorVertex (SSet.opFunctor.map H))
    (functorVertex (SSet.const (SSet.opObjEquiv.symm y)))
  have hb := hr.comp hp
  have h₁ :
      (hoFunctor.map ((pre j).app X.op)).toFunctor ⋙
        (hoFunctor.map ((pre (joinInr K.op (Δ[0] : SSet.{u}))).app X.op)).toFunctor =
      (hoFunctor.map ((pre (joinInr K.op (Δ[0] : SSet.{u}) ≫ j)).app X.op)).toFunctor := by
    rw [← Cat.Hom.comp_toFunctor, ← CategoryTheory.Functor.map_comp,
      ← NatTrans.comp_app, ← pre_map]
  change Function.Bijective
    (((hoFunctor.map ((pre j).app X.op)).toFunctor ⋙
      (hoFunctor.map ((pre (joinInr K.op (Δ[0] : SSet.{u}))).app X.op)).toFunctor).map :
      FunctorHom (SSet.opFunctor.map H) (SSet.const (SSet.opObjEquiv.symm y)) → _) at hb
  rw [h₁, hs] at hb
  have h₂ :
      (hoFunctor.map ((pre (t ≫ SSet.opFunctor.map (joinInl (Δ[0] : SSet.{u}) K))).app
        X.op)).toFunctor =
      (hoFunctor.map ((pre (SSet.opFunctor.map (joinInl (Δ[0] : SSet.{u}) K))).app
        X.op)).toFunctor ⋙ (hoFunctor.map ((pre t).app X.op)).toFunctor := by
    rw [← Cat.Hom.comp_toFunctor, ← CategoryTheory.Functor.map_comp,
      ← NatTrans.comp_app, ← pre_map]
  rw [h₂] at hb
  change Function.Bijective
    (((hoFunctor.map ((pre t).app X.op)).toFunctor.map) ∘
      ((hoFunctor.map ((pre (SSet.opFunctor.map (joinInl (Δ[0] : SSet.{u}) K))).app
        X.op)).toFunctor.map) :
      FunctorHom (SSet.opFunctor.map H) (SSet.const (SSet.opObjEquiv.symm y)) → _) at hb
  exact hb.of_comp_left (htf.homotopyCategoryMap_bijective _ _).injective

end SerrePositivity.InfinityCategories.F2.Presentable
