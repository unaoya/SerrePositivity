module

public import SerrePositivity.InfinityCategories.Core.PinchedSlice

/-!
概要：最後の外側ホーンの点との join による表示。
方針：標準単体の join における欠けた頂点を計算する。
規約：最後の面だけを含まないホーン。
使われ方：HTT §1.2.12、Kerodon §4.7.3 の終対象の同型不変性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：境界と点の join は最後のホーンの逆像。
方針：右側の頂点が唯一の除外頂点なので、欠落は左側の境界で生じる。
規約：n=0 も許す。
使われ方：HTT §1.2.12、Kerodon §4.7.3 の錐の延長。 -/
lemma finalHornPointJoin_preimage (n : ℕ) :
    (horn (n + 1) (Fin.last (n + 1))).preimage (joinStdSimplexIso.{u} n 0).hom =
      joinSubcomplexLeft (boundary n) Δ[0] := by
  ext ⟨⟨d⟩⟩ s
  change ((joinStdSimplexIso n 0).hom.app (Opposite.op ⦋d⦌) s ∈
    (horn (n + 1) (Fin.last (n + 1))).obj _) ↔ _
  have hw : Fin.last (n + 1) =
      Fin.cast (by omega) (Fin.last (n + 1) : Fin ((n + 1) + (0 + 1))) := rfl
  rw [hw, Join.mem_horn_joinStdSimplexIso_iff n 0 d s (Fin.last (n + 1)),
    Join.mem_joinSubcomplexLeft,
    Join.augMem_boundary_iff, Join.stdEncode, Join.missing_concat_iff]
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
使われ方：HTT §1.2.12、Kerodon §4.7.3 の境界上の錐。 -/
noncomputable def finalHornPointJoinIso (n : ℕ) :
    join (boundary n : SSet.{u}) Δ[0] ≅ horn (n + 1) (Fin.last (n + 1)) :=
  joinSubcomplexLeftIso (boundary n) Δ[0] ≪≫
    Subcomplex.eqToIso (finalHornPointJoin_preimage n).symm ≪≫
      subcomplexPreimageIso _ (joinStdSimplexIso n 0)

/-- 概要：最後のホーンの join 表示は包含と可換。
方針：像への射と逆像への射を包含の公式で消去する。
規約：左の因子は境界包含で写す。
使われ方：HTT §1.2.12、Kerodon §4.7.3 の充填の移送。 -/
lemma finalHornPointJoinIso_hom_ι (n : ℕ) :
    (finalHornPointJoinIso.{u} n).hom ≫ (horn (n + 1) (Fin.last (n + 1))).ι =
      joinMap (boundary n).ι (𝟙 Δ[0]) ≫ (joinStdSimplexIso n 0).hom := by
  change (((joinSubcomplexLeftIso (boundary n) Δ[0]).hom ≫
    Subcomplex.homOfLE (finalHornPointJoin_preimage n).symm.le) ≫
      (horn (n + 1) (Fin.last (n + 1))).fromPreimage (joinStdSimplexIso n 0).hom) ≫ _ = _
  rw [Category.assoc, Subcomplex.fromPreimage_ι, ← Category.assoc]
  rw [Category.assoc (joinSubcomplexLeftIso (boundary n) Δ[0]).hom,
    Subcomplex.homOfLE_ι, joinSubcomplexLeftIso_hom_ι]

/-- 概要：境界と点の join の最後の辺は最後のホーンの最後の辺。
方針：ホーン包含で単射性を使い、join の自然性で標準辺へ戻す。
規約：境界の最後の頂点と追加した頂点を結ぶ。
使われ方：HTT Proposition 1.2.4.3、終対象の同型不変性。 -/
lemma finalHornPointJoinIso_edge (n : ℕ) :
    SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
      joinMap (boundaryVertex n (Fin.last (n + 1))) (𝟙 Δ[0]) ≫
        (finalHornPointJoinIso.{u} (n + 1)).hom) = finalHornEdge n := by
  apply Subtype.ext
  change SSet.yonedaEquiv (((joinStdSimplexIso 0 0).inv ≫
    joinMap (boundaryVertex n (Fin.last (n + 1))) (𝟙 Δ[0]) ≫
      (finalHornPointJoinIso (n + 1)).hom) ≫ (horn (n + 2) (Fin.last (n + 2))).ι) = _
  rw [Category.assoc, Category.assoc, finalHornPointJoinIso_hom_ι,
    ← Category.assoc (joinMap _ _) (joinMap _ _), ← joinMap_comp,
    boundaryVertex_ι, Category.id_comp]
  have hv : SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (Fin.last (n + 1))) =
      stdSimplex.map (PinchedHom.lastVertex n) := by
    apply SSet.yonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    apply stdSimplex.ext
    intro i
    rfl
  rw [hv, joinStdSimplexIso_rightPoint_naturality, Iso.inv_hom_id_assoc]
  apply stdSimplex.ext
  intro i
  fin_cases i
  · apply Fin.ext
    change (PinchedHom.extendOrderHom
      (PinchedHom.lastVertex n).toOrderHom (0 : Fin 2)).val = n + 1
    rw [show (0 : Fin 2) = (0 : Fin 1).castSucc from rfl,
      PinchedHom.extendOrderHom_castSucc]
    rfl
  · apply Fin.ext
    change (PinchedHom.extendOrderHom
      (PinchedHom.lastVertex n).toOrderHom (1 : Fin 2)).val = n + 2
    rw [show (1 : Fin 2) = Fin.last 1 from rfl, PinchedHom.extendOrderHom_last]
    rfl

end SerrePositivity.InfinityCategories
