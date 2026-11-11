module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedSlice

/-!
概要：最後の外側ホーンの点との join による表示。
方針：標準単体の join における欠けた頂点を計算する。
規約：最後の面だけを含まないホーン。
使われ方：HTT §1.2.12、Kerodon §4.7.3（Tag 02H6） の終対象の同型不変性。

対応節は Kerodon 4.7（Tag 05EA）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories

/-- 概要：境界と点の join は最後のホーンの逆像。
方針：右側の頂点が唯一の除外頂点なので、欠落は左側の境界で生じる。
規約：n=0 も許す。
使われ方：HTT §1.2.12、Kerodon §4.7.3（Tag 02H6） の錐の延長。 -/
lemma finalHornPointJoin_preimage (n : ℕ) :
    (horn (n + 1) (Fin.last (n + 1))).preimage (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} n 0).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexLeft (boundary n) Δ[0] := by
  ext ⟨⟨d⟩⟩ s
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom.app (Opposite.op ⦋d⦌) s ∈
    (horn (n + 1) (Fin.last (n + 1))).obj _) ↔ _
  have hw : Fin.last (n + 1) =
      Fin.cast (by omega) (Fin.last (n + 1) : Fin ((n + 1) + (0 + 1))) := rfl
  rw [hw, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.mem_horn_joinStdSimplexIso_iff n 0 d s (Fin.last (n + 1)),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.mem_joinSubcomplexLeft,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.augMem_boundary_iff, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdEncode, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.missing_concat_iff]
  constructor
  · rintro (⟨v, _, hv⟩ | ⟨v, hv, _⟩)
    · exact ⟨v, hv⟩
    · have h : v.natAdd (n + 1) = Fin.last (n + 1) := by
        have : v = 0 := Fin.ext (by have := v.isLt; omega)
        subst v
        rfl
      exact (hv h).elim
  · rintro ⟨v, hv⟩
    refine Or.inl ⟨v, ?_, hv⟩
    intro h
    have := congrArg Fin.val h
    have := v.isLt
    simp only [Fin.val_castAdd, Fin.val_last] at *
    omega

/-- 概要：境界と点の join は最後の外側ホーンと同型。
方針：join の像と逆像の二つの同型を合成する。
規約：標的は標準単体の最後のホーン。
使われ方：HTT §1.2.12、Kerodon §4.7.3（Tag 02H6） の境界上の錐。 -/
noncomputable def finalHornPointJoinIso (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (boundary n : SSet.{u}) Δ[0] ≅ horn (n + 1) (Fin.last (n + 1)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexLeftIso (boundary n) Δ[0] ≪≫
    Subcomplex.eqToIso (finalHornPointJoin_preimage n).symm ≪≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.subcomplexPreimageIso _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0)

/-- 概要：最後のホーンの join 表示は包含と可換。
方針：像への射と逆像への射を包含の公式で消去する。
規約：左の因子は境界包含で写す。
使われ方：HTT §1.2.12、Kerodon §4.7.3（Tag 02H6） の充填の移送。 -/
lemma finalHornPointJoinIso_hom_ι (n : ℕ) :
    (finalHornPointJoinIso.{u} n).hom ≫ (horn (n + 1) (Fin.last (n + 1))).ι =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (boundary n).ι (𝟙 Δ[0]) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom := by
  change (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexLeftIso (boundary n) Δ[0]).hom ≫
    Subcomplex.homOfLE (finalHornPointJoin_preimage n).symm.le) ≫
      (horn (n + 1) (Fin.last (n + 1))).fromPreimage (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom) ≫ _ = _
  rw [Category.assoc, Subcomplex.fromPreimage_ι, ← Category.assoc]
  rw [Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexLeftIso (boundary n) Δ[0]).hom,
    Subcomplex.homOfLE_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexLeftIso_hom_ι]

/-- 概要：境界と点の join の最後の辺は最後のホーンの最後の辺。
方針：ホーン包含で単射性を使い、join の自然性で標準辺へ戻す。
規約：境界の最後の頂点と追加した頂点を結ぶ。
使われ方：HTT Proposition 1.2.4.3、終対象の同型不変性。 -/
lemma finalHornPointJoinIso_edge (n : ℕ) :
    SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1))) (𝟙 Δ[0]) ≫
        (finalHornPointJoinIso.{u} (n + 1)).hom) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge n := by
  apply Subtype.ext
  change SSet.yonedaEquiv (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1))) (𝟙 Δ[0]) ≫
      (finalHornPointJoinIso (n + 1)).hom) ≫ (horn (n + 2) (Fin.last (n + 2))).ι) = _
  rw [Category.assoc, Category.assoc, finalHornPointJoinIso_hom_ι,
    ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _ _), ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex_ι, Category.id_comp]
  have hv : SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (Fin.last (n + 1))) =
      stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex n) := by
    apply SSet.yonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    apply stdSimplex.ext
    intro i
    rfl
  rw [hv, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinStdSimplexIso_rightPoint_naturality, Iso.inv_hom_id_assoc]
  apply stdSimplex.ext
  intro i
  fin_cases i
  · apply Fin.ext
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex n).toOrderHom (0 : Fin 2)).val = n + 1
    rw [show (0 : Fin 2) = (0 : Fin 1).castSucc from rfl,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc]
    rfl
  · apply Fin.ext
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex n).toOrderHom (1 : Fin 2)).val = n + 2
    rw [show (1 : Fin 2) = Fin.last 1 from rfl, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last]
    rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
