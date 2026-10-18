module
public import SerrePositivity.InfinityCategories.Stable.CoconeTransportPrism
public import SerrePositivity.InfinityCategories.Stable.CoconeRestrictionCartesianEdge
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy

/-! # 余錐の制限射の辺の持ち上げ

概要：図式の辺を、終点の余錐を固定して cartesian な辺へ持ち上げる。
方針：図式の辺を prism に直し、頂点を固定した余錐の輸送を使う。
規約：形状は任意の単体集合。使われ方：余錐の相対充填の輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：終点を指定した図式の辺には cartesian な余錐の持ち上げがある。
方針：頂点を固定した prism を curry し、頂点で恒等な辺の cartesian 性を使う。
規約：値域は quasicategory、形状は任意。
使われ方：余錐の制限の反転を cocartesian fibration として認証する。 -/
lemma exists_cartesian_cocone_lift (K X : SSet.{u}) [Quasicategory X]
    (v : ((ihom (join K (Δ[0] : SSet.{u}))).obj X) _⦋0⦌)
    (b : ((ihom K).obj X) _⦋0⦌)
    (a : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom K).obj X)) b
      ((coconeRestriction K X).app (Opposite.op ⦋0⦌) v)) :
    ∃ (w : ((ihom (join K (Δ[0] : SSet.{u}))).obj X) _⦋0⦌)
      (e : SSet.Truncated.Edge
        (X := (truncation 2).obj ((ihom (join K (Δ[0] : SSet.{u}))).obj X)) w v),
      (coconeRestriction K X).app (Opposite.op ⦋1⦌) e.edge = a.edge ∧
        IsCartesianEdge (coconeRestriction K X) e.edge := by
  let T := join K (Δ[0] : SSet.{u})
  let F := (functorVertexEquiv T X).symm v
  have hF : functorVertex F = v := (functorVertexEquiv T X).apply_symm_apply _
  let β : (Δ[1] : SSet.{u}) ⟶ (ihom K).obj X := SSet.yonedaEquiv.symm a.edge
  let H := (β_ (Δ[1] : SSet.{u}) K).hom ≫ uncurry β
  have hH : prismEndpoint 1 K ≫ H = joinInl K Δ[0] ≫ F := by
    apply functorVertex_injective
    change functorVertex (SSet.ι₁ ≫ uncurry β) = _
    rw [functorVertex_uncurry_one]
    change ((ihom K).obj X).δ 0 a.edge =
      (coconeRestriction K X).app (Opposite.op ⦋0⦌) (functorVertex F)
    rw [hF]
    exact a.tgt_eq
  obtain ⟨L, hL₁, hLK, hLv⟩ := exists_cocone_fixedVertex_prism F H hH
  let l := curry ((β_ T (Δ[1] : SSet.{u})).hom ≫ L)
  let s := SSet.yonedaEquiv l
  have hs₁ : ((ihom T).obj X).δ 0 s = v := by
    rw [← functorVertex_uncurry_one, Equiv.symm_apply_apply]
    dsimp only [l]
    rw [uncurry_curry]
    have hs : SSet.ι₁ ≫ (β_ T (Δ[1] : SSet.{u})).hom = prismEndpoint 1 T := rfl
    rw [← Category.assoc, hs, hL₁, hF]
  let e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom T).obj X))
      (((ihom T).obj X).δ 1 s) v := ⟨s, rfl, hs₁⟩
  have hl : l ≫ coconeRestriction K X = β := by
    apply uncurry_injective
    dsimp only [l]
    rw [coconeRestriction, uncurry_pre_app, uncurry_curry]
    have hs : (joinInl K (Δ[0] : SSet.{u}) ▷ Δ[1]) ≫ (β_ T (Δ[1] : SSet.{u})).hom =
        (β_ K (Δ[1] : SSet.{u})).hom ≫ (Δ[1] ◁ joinInl K Δ[0]) := rfl
    rw [← Category.assoc, hs, Category.assoc, hLK]
    dsimp only [H]
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
  refine ⟨_, e, ?_, isCartesianEdge_coconeRestriction_of_apex e ?_⟩
  · change (coconeRestriction K X).app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv l) = a.edge
    rw [← SSet.yonedaEquiv_comp, hl, Equiv.apply_symm_apply]
  · let z := F.app (Opposite.op ⦋0⦌)
      ((joinInr K (Δ[0] : SSet.{u})).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
    have heq : (e.map ((truncation 2).map (coconeApexEvaluation K X))).edge =
        PinchedHom.constant z 1 := by
      let w : ((Δ[1] : SSet.{u}) ⊗ Δ[0]) _⦋1⦌ :=
        ⟨SSet.yonedaEquiv (𝟙 Δ[1]),
          PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) 1⟩
      have hh := ConcreteCategory.congr_hom (NatTrans.congr_app hLv (Opposite.op ⦋1⦌)) w
      change L.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 Δ[1]),
          (joinInr K (Δ[0] : SSet.{u})).app (Opposite.op ⦋1⦌)
            (PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) 1)) =
        F.app (Opposite.op ⦋1⦌) ((joinInr K (Δ[0] : SSet.{u})).app (Opposite.op ⦋1⦌)
          (PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) 1)) at hh
      rw [pinchedConstant_map, pinchedConstant_map] at hh
      exact hh
    have hinv := isEquivalencePathVertex_const z
    unfold IsEquivalencePathVertex at hinv
    rw [intervalFunctorVertexEdge_functorVertex] at hinv
    exact (isInvertibleEdge_congr heq).2 hinv

end SerrePositivity.InfinityCategories
