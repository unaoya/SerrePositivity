module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.BaseChange
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismFilling

/-!
概要：cocartesian な最初の垂直辺を持つ相対 prism の延長。
方針：prism の正則 pairing の内セルを inner fibration、外セルを指定辺で充填する。
規約：底が標準 prism の場合に、全頂点を含む部分複体上の一致から底を固定する。
使われ方：Kerodon Lemma 5.2.2.13（Tag 02RB）、一般の covariant transport の存在証明。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：標準 prism 上の inner fibration の部分切断は cocartesian な先頭辺の下で延長できる。
方針：底の射の頂点による一意性で全段階の底を固定して pairing のセルを充填する。
規約：標準 prism の右因子は正次元。
使われ方：Kerodon Lemma 5.2.2.13（Tag 02RB） の相対的なセル分解。 -/
lemma cocartesian_prism_exists_section {E : SSet.{u}} (n : ℕ)
    (p : E ⟶ (Δ[1] : SSet.{u}) ⊗ Δ[n + 1]) [InnerFibration p]
    (a : (Subcomplex.unionProd (horn 1 0) (boundary (n + 1)) : SSet.{u}) ⟶ E)
    (ha : a ≫ p = (Subcomplex.unionProd (horn 1 0) (boundary (n + 1))).ι)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (a.app (Opposite.op ⦋1⦌)
      ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstVerticalEdge (n + 1), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstVerticalEdge_mem n⟩)) :
    ∃ F : (Δ[1] : SSet.{u}) ⊗ Δ[n + 1] ⟶ E,
      (Subcomplex.unionProd (horn 1 0) (boundary (n + 1))).ι ≫ F = a ∧
        F ≫ p = 𝟙 _ := by
  let Q := prodStdSimplex.pairingCore.{u} (0 : Fin 1) (n + 1)
  have := (Q.isProper_pairing_iff).1 (inferInstance : Q.pairing.IsProper)
  have h : ∃ F : (Δ[1] : SSet.{u}) ⊗ Δ[n + 1] ⟶ E,
      (Subcomplex.unionProd (horn 1 0) (boundary (n + 1))).ι ≫ F = a := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.pairing_exists_extension Q.pairing a
    intro j g hg
    have hgp₀ : (g ≫ p).app (Opposite.op ⦋0⦌) =
        (Q.pairing.rankFunction.filtration j).ι.app (Opposite.op ⦋0⦌) := by
      apply ConcreteCategory.hom_ext
      intro v
      let w : (Subcomplex.unionProd (horn 1 0) (boundary (n + 1)) : SSet.{u}) _⦋0⦌ :=
        ⟨v.val, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismDomain_contains_vertices n v.val⟩
      have hh := ConcreteCategory.congr_hom (NatTrans.congr_app hg (Opposite.op ⦋0⦌)) w
      have hh' := congrArg (fun z ↦ p.app (Opposite.op ⦋0⦌) z) hh
      have hh'' := ConcreteCategory.congr_hom (NatTrans.congr_app ha (Opposite.op ⦋0⦌)) w
      exact hh'.trans hh''
    have hgp : g ≫ p = (Q.pairing.rankFunction.filtration j).ι := by
      apply CartesianMonoidalCategory.hom_ext
      · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
        simpa only [NatTrans.comp_app, Category.assoc] using
          congrArg (fun z ↦ z ≫ (fst (Δ[1] : SSet.{u}) Δ[n + 1]).app (Opposite.op ⦋0⦌)) hgp₀
      · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
        simpa only [NatTrans.comp_app, Category.assoc] using
          congrArg (fun z ↦ z ≫ (snd (Δ[1] : SSet.{u}) Δ[n + 1]).app (Opposite.op ⦋0⦌)) hgp₀
    intro c
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
    have sq : CommSq (c.mapHorn ≫ g) c.horn.ι p c.map := by
      constructor
      rw [Category.assoc, hgp, c.mapHorn_ι]
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
      have sq₀ : CommSq σ (horn (n + 2) 0).ι p c.map := by
        constructor
        dsimp only [σ]
        rw [Category.assoc, sq.w]
        rfl
      have := hc n σ c.map hσ sq₀
      let F := sq₀.lift
      have hF : (horn (n + 2) 0).ι ≫ F = σ := sq₀.fac_left
      refine ⟨F, ?_⟩
      have he : e.inv ≫ (horn (n + 2) 0).ι = c.horn.ι := rfl
      rw [← he, Category.assoc, hF]
      exact e.inv_hom_id_assoc _
    · have h0 : 0 < c.index := by
        rw [hci]
        exact Fin.pos_iff_ne_zero.mpr (fun h ↦ hi0
          (Fin.ext (congrArg (fun k : Fin (n + 3) ↦ k.val) h)))
      have hn : c.index < Fin.last (n + 2) := by rw [hci]; exact Fin.castSucc_lt_last _
      have : HasLiftingProperty c.horn.ι p :=
        InnerFibration.mem (q := p) _ (innerHornInclusions.intro c.index h0 hn)
      exact ⟨sq.lift, sq.fac_left⟩
  obtain ⟨F, hF⟩ := h
  refine ⟨F, hF, ?_⟩
  apply CartesianMonoidalCategory.hom_ext
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_of_subcomplex_vertices _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismDomain_contains_vertices n)
    rw [← Category.assoc, ← Category.assoc, hF, ha]
    rfl
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_of_subcomplex_vertices _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismDomain_contains_vertices n)
    rw [← Category.assoc, ← Category.assoc, hF, ha]
    rfl

/-- 概要：cocartesian な最初の垂直辺を持つ prism は底の全図式を固定して持ち上げられる。
方針：底の prism に引き戻し、標準 prism 上の部分切断を延長する。
規約：全空間と底の quasicategory 性は不要。
使われ方：Kerodon Lemma 5.2.2.13（Tag 02RB）、cocartesian transport の相対的な延長。 -/
lemma cocartesian_prism_exists_lift {E B : SSet.{u}} (p : E ⟶ B) [InnerFibration p]
    (n : ℕ)
    (a : (Subcomplex.unionProd (horn 1 0) (boundary (n + 1)) : SSet.{u}) ⟶ E)
    (b : (Δ[1] : SSet.{u}) ⊗ Δ[n + 1] ⟶ B)
    (ha : a ≫ p = (Subcomplex.unionProd (horn 1 0) (boundary (n + 1))).ι ≫ b)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (a.app (Opposite.op ⦋1⦌)
      ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstVerticalEdge (n + 1), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstVerticalEdge_mem n⟩)) :
    ∃ F : (Δ[1] : SSet.{u}) ⊗ Δ[n + 1] ⟶ E,
      (Subcomplex.unionProd (horn 1 0) (boundary (n + 1))).ι ≫ F = a ∧ F ≫ p = b := by
  let q := pullback.snd p b
  have : InnerFibration q := ⟨innerFibrations.pullback_snd p b (InnerFibration.mem (q := p))⟩
  let a' := pullback.lift a
    (Subcomplex.unionProd (horn 1 0) (boundary (n + 1))).ι ha
  have ha' : a' ≫ q = (Subcomplex.unionProd (horn 1 0) (boundary (n + 1))).ι :=
    pullback.lift_snd _ _ _
  have hc' : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q (a'.app (Opposite.op ⦋1⦌)
      ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstVerticalEdge (n + 1), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstVerticalEdge_mem n⟩) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_pullback
    change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p ((a' ≫ pullback.fst p b).app (Opposite.op ⦋1⦌) _)
    rw [pullback.lift_fst]
    exact hc
  obtain ⟨F, hF, hFq⟩ := cocartesian_prism_exists_section n q a' ha' hc'
  refine ⟨F ≫ pullback.fst p b, ?_, ?_⟩
  · rw [← Category.assoc, hF, pullback.lift_fst]
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hFq, Category.id_comp]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
