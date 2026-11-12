module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.InitialHornProductPairing

/-!
概要：最初の外側ホーンと標準単体の積の可逆な辺を用いた延長。
方針：正則 pairing の最初の外側ホーンを可逆性で、他の内ホーンを quasicategory 性で埋める。
規約：指定した最初の辺の像だけに可逆性を仮定する。
使われ方：Kerodon §5.3.7（Tag 01US） の錐の制限の cocartesian な辺。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：最初の外側ホーンと境界の積の和上の射は指定した最初の辺が可逆なら積全体へ延長する。
方針：正則 pairing の零番目のホーンを可逆辺で充填し、残りの内ホーンを埋める。
規約：E は quasicategory、左のホーンの次元は二以上、右因子の次元は任意。
使われ方：Kerodon §5.3.7（Tag 01US） の相対的な錐のホーン充填。 -/
lemma initialHornProduct_exists_extension_of_invertible_firstEdge {E : SSet.{u}} [Quasicategory E]
    (m n : ℕ) (a : (Subcomplex.unionProd (horn (m + 2) 0) (boundary n) : SSet.{u}) ⟶ E)
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (a.app (Opposite.op ⦋1⦌)
      ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.initialHornProductFirstEdge m n, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.initialHornProductFirstEdge_mem m n⟩))) :
    ∃ F : (Δ[m + 2] : SSet.{u}) ⊗ Δ[n] ⟶ E,
      (Subcomplex.unionProd (horn (m + 2) 0) (boundary n)).ι ≫ F = a := by
  let Q := prodStdSimplex.pairingCore.{u} (0 : Fin (m + 2)) n
  have := (Q.isProper_pairing_iff).1 (inferInstance : Q.pairing.IsProper)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.pairing_exists_extension Q.pairing a
  intro j g hg c
  rcases c with ⟨s, hs⟩
  obtain ⟨t, rfl⟩ := Q.equivII.surjective s
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.initialHornProductPairing_dim_ge m n t
  rcases t with ⟨x, d, hx, i, hi⟩
  dsimp only at hd
  cases d with
  | zero => omega
  | succ k =>
    let t : Q.ι := ⟨x, k + 1, hx, i, hi⟩
    let c : Q.pairing.rankFunction.Cell j := ⟨Q.equivII t, hs⟩
    change ∃ F : (Δ[k + 2] : SSet.{u}) ⟶ E, c.horn.ι ≫ F = c.mapHorn ≫ g
    have hci : c.index = i.castSucc := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.pairingCore_cell_index Q _ t hs
    have hcm : c.map = SSet.yonedaEquiv.symm (x.cast hx).simplex :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.pairingCore_cell_map Q _ t hs
    by_cases hi0 : i = 0
    · have hc0 : c.index = 0 := by rw [hci, hi0]; rfl
      let e := Subcomplex.eqToIso (congrArg (horn (k + 2)) hc0.symm)
      let σ := e.hom ≫ c.mapHorn ≫ g
      let v := (e.hom ≫ c.mapHorn).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge k)
      have hv : v = (Subcomplex.homOfLE (Q.pairing.rankFunction.le_filtration j)).app
          (Opposite.op ⦋1⦌)
            ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.initialHornProductFirstEdge m n, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.initialHornProductFirstEdge_mem m n⟩ := by
        apply Subtype.ext
        change c.map.app (Opposite.op ⦋1⦌)
          (stdSimplex.edge (k + 2) 0 1 (Fin.zero_le _)) = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.initialHornProductFirstEdge m n
        rw [hcm]
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.initialHornProductPairing_firstEdge_eq m n t hi0
      have hσ : σ.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge k) =
          a.app (Opposite.op ⦋1⦌)
            ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.initialHornProductFirstEdge m n, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.initialHornProductFirstEdge_mem m n⟩ := by
        change g.app (Opposite.op ⦋1⦌) v = _
        rw [hv]
        exact ConcreteCategory.congr_hom (NatTrans.congr_app hg (Opposite.op ⦋1⦌)) _
      let edge := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (σ.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge k))
      have hedge : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge edge := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr hσ).mpr ha
      obtain ⟨F, hF⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hasInitialHornFillers_of_isInvertibleEdge edge hedge k σ rfl
      refine ⟨F, ?_⟩
      have he : e.inv ≫ (horn (k + 2) 0).ι = c.horn.ι := rfl
      rw [← he, Category.assoc, hF]
      exact e.inv_hom_id_assoc _
    · have h0 : 0 < c.index := by
        rw [hci]
        exact Fin.pos_iff_ne_zero.mpr (fun h ↦ hi0
          (Fin.ext (congrArg (fun k : Fin (k + 3) ↦ k.val) h)))
      have hn : c.index < Fin.last (k + 2) := by rw [hci]; exact Fin.castSucc_lt_last _
      obtain ⟨F, hF⟩ := Quasicategory.hornFilling h0 hn (c.mapHorn ≫ g)
      exact ⟨F, hF.symm⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
