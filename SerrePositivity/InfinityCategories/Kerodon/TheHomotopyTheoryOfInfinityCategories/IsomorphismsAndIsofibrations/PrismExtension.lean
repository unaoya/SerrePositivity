module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismPairing

/-!
概要：可逆な最初の垂直辺を持つ prism の延長。
方針：内ホーンは quasicategory 性、零番目の外側ホーンは Joyal の定理で充填する。
規約：正次元の標準単体の prism を扱う。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の右ファイブレーション版。

対応節は Kerodon 4.4（Tag 01EM）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations

/-- 概要：先頭と境界の prism 上の射は、最初の垂直辺が可逆なら全体へ延長できる。
方針：正則 pairing の各セルを内ホーンまたは可逆辺を持つ零番目の外側ホーンとして充填する。
規約：終端の面も含めて prism 全体を延長する。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の prism のセル分解。 -/
lemma prism_exists_extension_of_invertible_firstEdge {E : SSet.{u}} [Quasicategory E]
    (n : ℕ) (a : (Subcomplex.unionProd (horn 1 0) (boundary (n + 1)) : SSet.{u}) ⟶ E)
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (a.app (Opposite.op ⦋1⦌)
      ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstVerticalEdge (n + 1), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstVerticalEdge_mem n⟩))) :
    ∃ F : (Δ[1] : SSet.{u}) ⊗ Δ[n + 1] ⟶ E,
      (Subcomplex.unionProd (horn 1 0) (boundary (n + 1))).ι ≫ F = a := by
  let Q := prodStdSimplex.pairingCore.{u} (0 : Fin 1) (n + 1)
  have := (Q.isProper_pairing_iff).1 (inferInstance : Q.pairing.IsProper)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.pairing_exists_extension Q.pairing a
  intro j g hg c
  rcases c with ⟨s, hs⟩
  obtain ⟨t, rfl⟩ := Q.equivII.surjective s
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismPairing_dim_eq (n + 1) t
  rcases t with ⟨x, d, hx, i, hi⟩
  dsimp only at hd
  subst d
  let t : Q.ι := ⟨x, n + 1, hx, i, hi⟩
  let c : Q.pairing.rankFunction.Cell j := ⟨Q.equivII t, hs⟩
  change ∃ F : (Δ[n + 2] : SSet.{u}) ⟶ E, c.horn.ι ≫ F = c.mapHorn ≫ g
  have hci : c.index = i.castSucc := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.pairingCore_cell_index Q _ t hs
  have hcm : c.map = SSet.yonedaEquiv.symm (x.cast hx).simplex :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.pairingCore_cell_map Q _ t hs
  by_cases hi0 : i = 0
  · have hc0 : c.index = 0 := by rw [hci, hi0]; rfl
    let e := Subcomplex.eqToIso (congrArg (horn (n + 2)) hc0.symm)
    let σ := e.hom ≫ c.mapHorn ≫ g
    let v := (e.hom ≫ c.mapHorn).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge n)
    have hv : v = (Subcomplex.homOfLE (Q.pairing.rankFunction.le_filtration j)).app
        (Opposite.op ⦋1⦌)
          ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstVerticalEdge (n + 1), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstVerticalEdge_mem n⟩ := by
      apply Subtype.ext
      change c.map.app (Opposite.op ⦋1⦌)
        (stdSimplex.edge (n + 2) 0 1 (Fin.zero_le _)) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstVerticalEdge (n + 1)
      rw [hcm]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismPairing_firstEdge_eq (n + 1) t hi0
    have hσ : σ.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge n) =
        a.app (Opposite.op ⦋1⦌)
          ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstVerticalEdge (n + 1), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstVerticalEdge_mem n⟩ := by
      change g.app (Opposite.op ⦋1⦌) v = _
      rw [hv]
      exact ConcreteCategory.congr_hom (NatTrans.congr_app hg (Opposite.op ⦋1⦌)) _
    let edge := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (σ.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge n))
    have hedge : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge edge := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr hσ).mpr ha
    obtain ⟨F, hF⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hasInitialHornFillers_of_isInvertibleEdge edge hedge n σ rfl
    refine ⟨F, ?_⟩
    have he : e.inv ≫ (horn (n + 2) 0).ι = c.horn.ι := rfl
    rw [← he, Category.assoc, hF]
    exact e.inv_hom_id_assoc _
  · have h0 : 0 < c.index := by
      rw [hci]
      exact Fin.pos_iff_ne_zero.mpr (fun h ↦ hi0
        (Fin.ext (congrArg (fun k : Fin (n + 3) ↦ k.val) h)))
    have hn : c.index < Fin.last (n + 2) := by rw [hci]; exact Fin.castSucc_lt_last _
    obtain ⟨F, hF⟩ := Quasicategory.hornFilling h0 hn (c.mapHorn ≫ g)
    exact ⟨F, hF.symm⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
