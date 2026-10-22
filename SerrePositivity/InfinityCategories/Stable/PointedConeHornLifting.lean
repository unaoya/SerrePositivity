module

public import SerrePositivity.InfinityCategories.Stable.PointedConeInitialHorn

/-!
概要：固定頂点からの全錐における二次元以上のホーン持ち上げ。
方針：二変数の交換後に両端を保って充填し、厳密な頂点 fiber に戻す。
規約：安定性や有限極限を仮定しない。使われ方：一般安定性判定の全錐比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 錐の頂点を厳密に固定した全錐の単体集合。 -/
def pointedConeFamily (K X : SSet.{u}) (x : X _⦋0⦌) : SSet.{u} :=
  vertexFiber (coneApexEvaluation K X) x

/-- 固定頂点からの錐を底の図式へ送る制限射。 -/
def pointedConeProjection (K X : SSet.{u}) (x : X _⦋0⦌) :
    pointedConeFamily K X x ⟶ (ihom K).obj X :=
  vertexFiberι (coneApexEvaluation K X) x ≫ coneRestriction K X

/-- 固定頂点の厳密 fiber で二次元以上の先頭ホーンを持ち上げる。 -/
lemma pointedCone_initialHorn_lift {K X : SSet.{u}} [Quasicategory X]
    (x : X _⦋0⦌) (m : ℕ)
    (a : (horn (m + 2) 0 : SSet.{u}) ⟶ pointedConeFamily K X x)
    (β : (Δ[m + 2] : SSet.{u}) ⟶ (ihom K).obj X)
    (hw : a ≫ pointedConeProjection K X x = (horn (m + 2) 0).ι ≫ β) :
    ∃ F : (Δ[m + 2] : SSet.{u}) ⟶ pointedConeFamily K X x,
      (horn (m + 2) 0).ι ≫ F = a ∧ F ≫ pointedConeProjection K X x = β := by
  let D := join (Δ[0] : SSet.{u}) K
  let α := a ≫ vertexFiberι (coneApexEvaluation K X) x
  let b := internalHomFlipHomEquiv (horn (m + 2) 0 : SSet.{u}) D X α
  let c := internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) K X β
  let c₀ : (Δ[0] : SSet.{u}) ⟶ (ihom (Δ[m + 2] : SSet.{u})).obj X :=
    SSet.const (functorVertex (SSet.const x))
  have hc : c ≫ (pre (horn (m + 2) 0).ι).app X = joinInr Δ[0] K ≫ b := by
    have hh := congrArg (internalHomFlipHomEquiv (horn (m + 2) 0 : SSet.{u}) K X) hw
    change internalHomFlipHomEquiv _ K X (α ≫ (pre (joinInr Δ[0] K)).app X) = _ at hh
    rw [internalHomFlipHomEquiv_pre_app (joinInr Δ[0] K) α,
      internalHomFlipHomEquiv_pre (horn (m + 2) 0).ι β] at hh
    exact hh.symm
  have hc₀ : c₀ ≫ (pre (horn (m + 2) 0).ι).app X = joinInl Δ[0] K ≫ b := by
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_natural_left]
    dsimp [b, internalHomFlipHomEquiv]
    rw [uncurry_curry]
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨t, v⟩
    have hx := (a.app (Opposite.op ⦋n⦌) t).property
    change (coneApexEvaluation K X).app (Opposite.op ⦋n⦌)
      (α.app (Opposite.op ⦋n⦌) t) = PinchedHom.constant x n at hx
    have hv : v = PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) n :=
      by
        apply stdSimplex.ext
        intro j
        exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm
    subst v
    change PinchedHom.constant x n = _
    change PinchedHom.constant x n = (uncurry α).app (Opposite.op ⦋n⦌)
      ((joinInl (Δ[0] : SSet.{u}) K).app (Opposite.op ⦋n⦌)
        (PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) n), t)
    rw [pinchedConstant_map]
    exact hx.symm
  have he : IsInvertibleEdge (edgeOfSimplex ((uncurry b).app (Opposite.op ⦋1⦌)
      (initialHornEdge m, PinchedHom.constant
        ((joinInl (Δ[0] : SSet.{u}) K).app (Opposite.op ⦋0⦌)
          (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) 1))) := by
    have hx := (a.app (Opposite.op ⦋1⦌) (initialHornEdge m)).property
    have hconst : (uncurry b).app (Opposite.op ⦋1⦌)
        (initialHornEdge m, PinchedHom.constant
          ((joinInl (Δ[0] : SSet.{u}) K).app (Opposite.op ⦋0⦌)
            (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) 1) = PinchedHom.constant x 1 := by
      exact hx
    apply (isInvertibleEdge_congr
      (e := edgeOfSimplex _) (f := edgeOfSimplex (PinchedHom.constant x 1)) hconst).2
    have hh := isEquivalencePathVertex_const x
    unfold IsEquivalencePathVertex at hh
    rw [intervalFunctorVertexEdge_functorVertex] at hh
    exact hh
  obtain ⟨G, hG₀, hGk, hGb⟩ := pointedCone_initialHorn_extend m c₀ c b hc₀ hc he
  let F := (internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) D X).symm G
  have hF : internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) D X F = G :=
    (internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) D X).apply_symm_apply G
  have hFa : (horn (m + 2) 0).ι ≫ F = α := by
    apply (internalHomFlipHomEquiv (horn (m + 2) 0 : SSet.{u}) D X).injective
    rw [internalHomFlipHomEquiv_pre, hF]
    exact hGb
  have hFk : F ≫ coneRestriction K X = β := by
    apply (internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) K X).injective
    change internalHomFlipHomEquiv _ K X (F ≫ (pre (joinInr Δ[0] K)).app X) = _
    rw [internalHomFlipHomEquiv_pre_app, hF]
    exact hGk
  have hFx : F ≫ coneApexEvaluation K X = SSet.const x := by
    have hh := congrArg uncurry hG₀
    rw [uncurry_natural_left] at hh
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro t
    let w : ((Δ[m + 2] : SSet.{u}) ⊗ Δ[0]) _⦋n⦌ :=
      ⟨t, PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) n⟩
    have hz := ConcreteCategory.congr_hom (NatTrans.congr_app hh (Opposite.op ⦋n⦌)) w
    rw [← hF] at hz
    simp only [internalHomFlipHomEquiv, Equiv.coe_fn_mk, uncurry_curry] at hz
    change (uncurry F).app (Opposite.op ⦋n⦌)
      ((joinInl (Δ[0] : SSet.{u}) K).app (Opposite.op ⦋n⦌)
        (PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) n), t) =
          PinchedHom.constant x n at hz
    rw [pinchedConstant_map] at hz
    exact hz
  refine ⟨vertexFiberLift _ x F hFx, ?_, ?_⟩
  · apply vertexFiber_hom_ext (coneApexEvaluation K X) x
    rw [Category.assoc, vertexFiberLift_ι]
    exact hFa
  · change vertexFiberLift _ x F hFx ≫ vertexFiberι _ x ≫ coneRestriction K X = _
    rw [← Category.assoc, vertexFiberLift_ι]
    exact hFk
/-- 固定頂点の厳密 fiber で任意の内ホーンを持ち上げる。 -/
lemma pointedCone_innerHorn_lift {K X : SSet.{u}} [Quasicategory X]
    (x : X _⦋0⦌) (m : ℕ) (k : Fin (m + 3))
    (hk₀ : 0 < k) (hk : k < Fin.last (m + 2))
    (a : (horn (m + 2) k : SSet.{u}) ⟶ pointedConeFamily K X x)
    (β : (Δ[m + 2] : SSet.{u}) ⟶ (ihom K).obj X)
    (hw : a ≫ pointedConeProjection K X x = (horn (m + 2) k).ι ≫ β) :
    ∃ F : (Δ[m + 2] : SSet.{u}) ⟶ pointedConeFamily K X x,
      (horn (m + 2) k).ι ≫ F = a ∧ F ≫ pointedConeProjection K X x = β := by
  let D := join (Δ[0] : SSet.{u}) K
  let α := a ≫ vertexFiberι (coneApexEvaluation K X) x
  let b := internalHomFlipHomEquiv (horn (m + 2) k : SSet.{u}) D X α
  let c := internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) K X β
  let c₀ : (Δ[0] : SSet.{u}) ⟶ (ihom (Δ[m + 2] : SSet.{u})).obj X :=
    SSet.const (functorVertex (SSet.const x))
  have hc : c ≫ (pre (horn (m + 2) k).ι).app X = joinInr Δ[0] K ≫ b := by
    have hh := congrArg (internalHomFlipHomEquiv (horn (m + 2) k : SSet.{u}) K X) hw
    change internalHomFlipHomEquiv _ K X (α ≫ (pre (joinInr Δ[0] K)).app X) = _ at hh
    rw [internalHomFlipHomEquiv_pre_app (joinInr Δ[0] K) α,
      internalHomFlipHomEquiv_pre (horn (m + 2) k).ι β] at hh
    exact hh.symm
  have hc₀ : c₀ ≫ (pre (horn (m + 2) k).ι).app X = joinInl Δ[0] K ≫ b := by
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_natural_left]
    dsimp [b, internalHomFlipHomEquiv]
    rw [uncurry_curry]
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨t, v⟩
    have hx := (a.app (Opposite.op ⦋n⦌) t).property
    change (coneApexEvaluation K X).app (Opposite.op ⦋n⦌)
      (α.app (Opposite.op ⦋n⦌) t) = PinchedHom.constant x n at hx
    have hv : v = PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) n :=
      by
        apply stdSimplex.ext
        intro j
        exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm
    subst v
    change PinchedHom.constant x n = _
    change PinchedHom.constant x n = (uncurry α).app (Opposite.op ⦋n⦌)
      ((joinInl (Δ[0] : SSet.{u}) K).app (Opposite.op ⦋n⦌)
        (PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) n), t)
    rw [pinchedConstant_map]
    exact hx.symm
  let i := coprod.desc (joinInl (Δ[0] : SSet.{u}) K) (joinInr (Δ[0] : SSet.{u}) K)
  let : Mono i := joinEndpointPair_mono _ _
  let γ := (internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) (Δ[0] ⨿ K) X).symm
    (coprod.desc c₀ c)
  have hγ : internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) (Δ[0] ⨿ K) X γ =
      coprod.desc c₀ c :=
    (internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) (Δ[0] ⨿ K) X).apply_symm_apply _
  have hw' : α ≫ (pre i).app X = (horn (m + 2) k).ι ≫ γ := by
    apply (internalHomFlipHomEquiv (horn (m + 2) k : SSet.{u}) (Δ[0] ⨿ K) X).injective
    rw [internalHomFlipHomEquiv_pre_app i α,
      internalHomFlipHomEquiv_pre (horn (m + 2) k).ι γ, hγ]
    apply coprod.hom_ext
    · simpa only [i, coprod.inl_desc_assoc] using hc₀.symm
    · simpa only [i, coprod.inr_desc_assoc] using hc.symm
  have := InnerFibration.mem (q := (pre i).app X) _
    (innerHornInclusions.intro k hk₀ hk)
  let sq : CommSq α (horn (m + 2) k).ι ((pre i).app X) γ := ⟨hw'⟩
  let G := internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) D X sq.lift
  have hGi : i ≫ G = coprod.desc c₀ c := by
    have hh := congrArg (internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) (Δ[0] ⨿ K) X)
      sq.fac_right
    rw [internalHomFlipHomEquiv_pre_app i sq.lift, hγ] at hh
    exact hh
  have hG₀ : joinInl Δ[0] K ≫ G = c₀ := by
    have hh := congrArg (fun q ↦ (coprod.inl : (Δ[0] : SSet.{u}) ⟶ Δ[0] ⨿ K) ≫ q) hGi
    simpa only [i, coprod.inl_desc, coprod.inl_desc_assoc] using hh
  have hGk : joinInr Δ[0] K ≫ G = c := by
    have hh := congrArg (fun q ↦ (coprod.inr : K ⟶ (Δ[0] : SSet.{u}) ⨿ K) ≫ q) hGi
    simpa only [i, coprod.inr_desc, coprod.inr_desc_assoc] using hh
  have hGb : G ≫ (pre (horn (m + 2) k).ι).app X = b := by
    have hh := congrArg (internalHomFlipHomEquiv (horn (m + 2) k : SSet.{u}) D X)
      sq.fac_left
    rw [internalHomFlipHomEquiv_pre (horn (m + 2) k).ι sq.lift] at hh
    exact hh
  let F := (internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) D X).symm G
  have hF : internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) D X F = G :=
    (internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) D X).apply_symm_apply G
  have hFa : (horn (m + 2) k).ι ≫ F = α := by
    apply (internalHomFlipHomEquiv (horn (m + 2) k : SSet.{u}) D X).injective
    rw [internalHomFlipHomEquiv_pre, hF]
    exact hGb
  have hFk : F ≫ coneRestriction K X = β := by
    apply (internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) K X).injective
    change internalHomFlipHomEquiv _ K X (F ≫ (pre (joinInr Δ[0] K)).app X) = _
    rw [internalHomFlipHomEquiv_pre_app, hF]
    exact hGk
  have hFx : F ≫ coneApexEvaluation K X = SSet.const x := by
    have hh := congrArg uncurry hG₀
    rw [uncurry_natural_left] at hh
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro t
    let w : ((Δ[m + 2] : SSet.{u}) ⊗ Δ[0]) _⦋n⦌ :=
      ⟨t, PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) n⟩
    have hz := ConcreteCategory.congr_hom (NatTrans.congr_app hh (Opposite.op ⦋n⦌)) w
    rw [← hF] at hz
    simp only [internalHomFlipHomEquiv, Equiv.coe_fn_mk, uncurry_curry] at hz
    change (uncurry F).app (Opposite.op ⦋n⦌)
      ((joinInl (Δ[0] : SSet.{u}) K).app (Opposite.op ⦋n⦌)
        (PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) n), t) =
          PinchedHom.constant x n at hz
    rw [pinchedConstant_map] at hz
    exact hz
  refine ⟨vertexFiberLift _ x F hFx, ?_, ?_⟩
  · apply vertexFiber_hom_ext (coneApexEvaluation K X) x
    rw [Category.assoc, vertexFiberLift_ι]
    exact hFa
  · change vertexFiberLift _ x F hFx ≫ vertexFiberι _ x ≫ coneRestriction K X = _
    rw [← Category.assoc, vertexFiberLift_ι]
    exact hFk
end SerrePositivity.InfinityCategories
