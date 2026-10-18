module

public import SerrePositivity.InfinityCategories.Core.PrismBaseDetection
public import SerrePositivity.InfinityCategories.Core.CocartesianEdgePullback
public import SerrePositivity.InfinityCategories.Core.CocartesianCoslice

/-!
概要：cocartesian な最初の垂直辺を持つ prism の相対延長。
方針：基底の prism へ引き戻して正則 pairing の外側ホーンと内ホーンを充填する。
規約：正次元の標準単体の先頭と境界の prism を固定する。
使われ方：Kerodon §5.1.1・§7.1.5 の cocartesian な輸送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：先頭と境界の prism は最初の垂直辺が cocartesian なら基底上で延長できる。
方針：引き戻しの pairing の内ホーンを inner fibration で、先頭の外側ホーンを cocartesian 性で充填する。
規約：元・標的の quasicategory 性は不要。
使われ方：Kerodon §5.1.1・§7.1.5 の相対的な輸送のセル分解。 -/
lemma prism_exists_lift_of_cocartesian_firstEdge {E B : SSet.{u}}
    (p : E ⟶ B) [InnerFibration p] (n : ℕ)
    (a : (Subcomplex.unionProd (horn 1 0) (boundary (n + 1)) : SSet.{u}) ⟶ E)
    (β : (Δ[1] : SSet.{u}) ⊗ Δ[n + 1] ⟶ B)
    (hw : a ≫ p = (Subcomplex.unionProd (horn 1 0) (boundary (n + 1))).ι ≫ β)
    (ha : HasCocartesianHornLifting p (edgeOfSimplex (a.app (Opposite.op ⦋1⦌)
      ⟨prismFirstVerticalEdge (n + 1), prismFirstVerticalEdge_mem n⟩))) :
    ∃ F : (Δ[1] : SSet.{u}) ⊗ Δ[n + 1] ⟶ E,
      (Subcomplex.unionProd (horn 1 0) (boundary (n + 1))).ι ≫ F = a ∧ F ≫ p = β := by
  let A := Subcomplex.unionProd (horn 1 0) (boundary (n + 1))
  let P := pullback p β
  let q := pullback.snd p β
  haveI : InnerFibration q := ⟨innerFibrations.pullback_snd p β (InnerFibration.mem (q := p))⟩
  let a' : (A : SSet.{u}) ⟶ P := pullback.lift a A.ι hw
  have haq : a' ≫ q = A.ι := pullback.lift_snd _ _ _
  have ha' : HasCocartesianHornLifting q (edgeOfSimplex (a'.app (Opposite.op ⦋1⦌)
      ⟨prismFirstVerticalEdge (n + 1), prismFirstVerticalEdge_mem n⟩)) := by
    let edge := edgeOfSimplex (a'.app (Opposite.op ⦋1⦌)
      ⟨prismFirstVerticalEdge (n + 1), prismFirstVerticalEdge_mem n⟩)
    have he : (edge.map ((truncation 2).map (pullback.fst p β))).edge =
        (edgeOfSimplex (a.app (Opposite.op ⦋1⦌)
          ⟨prismFirstVerticalEdge (n + 1), prismFirstVerticalEdge_mem n⟩)).edge :=
      ConcreteCategory.congr_hom (NatTrans.congr_app (pullback.lift_fst a A.ι hw)
        (Opposite.op ⦋1⦌)) _
    exact hasCocartesianHornLifting_pullback_of_fst p β edge
      ((hasCocartesianHornLifting_congr p he).2 ha)
  let Q := prodStdSimplex.pairingCore.{u} (0 : Fin 1) (n + 1)
  have := (Q.isProper_pairing_iff).1 (inferInstance : Q.pairing.IsProper)
  obtain ⟨F, hF⟩ := pairing_exists_extension Q.pairing a' (by
    intro j g hg c
    have hgq : g ≫ q = (Q.pairing.rankFunction.filtration j).ι :=
      subcomplex_extension_over_prodStdSimplex A _ (Q.pairing.rankFunction.le_filtration j)
        (prismDomain_contains_vertices n) q a' haq g hg
    rcases c with ⟨s, hs⟩
    obtain ⟨t, rfl⟩ := Q.equivII.surjective s
    have hd := prismPairing_dim_eq (n + 1) t
    rcases t with ⟨x, d, hx, i, hi⟩
    dsimp only at hd
    subst d
    let t : Q.ι := ⟨x, n + 1, hx, i, hi⟩
    let c : Q.pairing.rankFunction.Cell j := ⟨Q.equivII t, hs⟩
    change ∃ F : (Δ[n + 2] : SSet.{u}) ⟶ P, c.horn.ι ≫ F = c.mapHorn ≫ g
    have hci : c.index = i.castSucc := pairingCore_cell_index Q _ t hs
    have hcm : c.map = SSet.yonedaEquiv.symm (x.cast hx).simplex :=
      pairingCore_cell_map Q _ t hs
    by_cases hi0 : i = 0
    · have hc0 : c.index = 0 := by rw [hci, hi0]; rfl
      let e := Subcomplex.eqToIso (congrArg (horn (n + 2)) hc0.symm)
      let σ := e.hom ≫ c.mapHorn ≫ g
      let v := (e.hom ≫ c.mapHorn).app (Opposite.op ⦋1⦌) (initialHornEdge n)
      have hv : v = (Subcomplex.homOfLE (Q.pairing.rankFunction.le_filtration j)).app
          (Opposite.op ⦋1⦌)
            ⟨prismFirstVerticalEdge (n + 1), prismFirstVerticalEdge_mem n⟩ := by
        apply Subtype.ext
        change c.map.app (Opposite.op ⦋1⦌)
          (stdSimplex.edge (n + 2) 0 1 (Fin.zero_le _)) = prismFirstVerticalEdge (n + 1)
        rw [hcm]
        exact prismPairing_firstEdge_eq (n + 1) t hi0
      have hσ : σ.app (Opposite.op ⦋1⦌) (initialHornEdge n) =
          a'.app (Opposite.op ⦋1⦌)
            ⟨prismFirstVerticalEdge (n + 1), prismFirstVerticalEdge_mem n⟩ := by
        change g.app (Opposite.op ⦋1⦌) v = _
        rw [hv]
        exact ConcreteCategory.congr_hom (NatTrans.congr_app hg (Opposite.op ⦋1⦌)) _
      let edge := edgeOfSimplex (σ.app (Opposite.op ⦋1⦌) (initialHornEdge n))
      have hedge : HasCocartesianHornLifting q edge :=
        (hasCocartesianHornLifting_congr q hσ).2 ha'
      have hσq : σ ≫ q = (horn (n + 2) 0).ι ≫ c.map := by
        dsimp [σ]
        rw [Category.assoc, Category.assoc, hgq, c.mapHorn_ι, ← Category.assoc]
        rfl
      obtain ⟨F, hF, _⟩ := hedge n σ c.map rfl hσq
      refine ⟨F, ?_⟩
      have he : e.inv ≫ (horn (n + 2) 0).ι = c.horn.ι := rfl
      rw [← he, Category.assoc, hF]
      exact e.inv_hom_id_assoc _
    · have h0 : 0 < c.index := by
        rw [hci]
        exact Fin.pos_iff_ne_zero.mpr (fun h ↦ hi0
          (Fin.ext (congrArg (fun k : Fin (n + 3) ↦ k.val) h)))
      have hn : c.index < Fin.last (n + 2) := by rw [hci]; exact Fin.castSucc_lt_last _
      haveI : HasLiftingProperty c.horn.ι q :=
        InnerFibration.mem (q := q) c.horn.ι (innerHornInclusions.intro c.index h0 hn)
      have hw : CommSq (c.mapHorn ≫ g) c.horn.ι q c.map := by
        constructor
        rw [Category.assoc, hgq, c.mapHorn_ι]
      exact ⟨hw.lift, hw.fac_left⟩)
  change A.ι ≫ F = a' at hF
  have hFq : F ≫ q = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · apply stdSimplex_hom_ext_of_subcomplex_vertices A (prismDomain_contains_vertices n)
      rw [← Category.assoc, ← Category.assoc, hF, ← Category.assoc, haq]
      simp
    · apply stdSimplex_hom_ext_of_subcomplex_vertices A (prismDomain_contains_vertices n)
      rw [← Category.assoc, ← Category.assoc, hF, ← Category.assoc, haq]
      simp
  refine ⟨F ≫ pullback.fst p β, ?_, ?_⟩
  · rw [← Category.assoc, hF]
    exact pullback.lift_fst _ _ _
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hFq, Category.id_comp]

end SerrePositivity.InfinityCategories
