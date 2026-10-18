module

public import SerrePositivity.InfinityCategories.Core.HornPointJoin
public import SerrePositivity.InfinityCategories.Core.NerveCone

/-!
概要：最初の外側ホーンの点と境界の join による表示。
方針：標準単体の join の切断で欠落する頂点を右因子に分ける。
規約：最初の面だけを含まないホーン。
使われ方：Kerodon §5.1.1 の cocartesian な辺と coslice の充填。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：点と境界の join は最初のホーンの逆像。
方針：除外する最初の頂点以外の欠落は右因子の境界で生じる。
規約：n=0 も許す。
使われ方：Kerodon §5.1.1 の coslice の境界の表示。 -/
lemma initialPointHornJoin_preimage (n : ℕ) :
    (horn (n + 1) 0).preimage (pointJoinStdSimplexIso.{u} n).hom =
      joinSubcomplexRight Δ[0] (boundary n) := by
  ext ⟨⟨d⟩⟩ s
  change ((pointJoinStdSimplexIso n).hom.app (Opposite.op ⦋d⦌) s ∈
    (horn (n + 1) 0).obj _) ↔ _
  rw [mem_horn_iff_notMem_range, Join.mem_joinSubcomplexRight, Join.augMem_boundary_iff]
  have hv : (fun i ↦ (pointJoinStdSimplexIso n).hom.app (Opposite.op ⦋d⦌) s i) =
      (fun i ↦ Fin.cast (by omega) (Join.stdEncode 0 n d s i)) := by
    funext i
    apply Fin.ext
    exact pointJoinStdSimplexIso_hom_app_val n d s i
  have hw : (0 : Fin (n + 2)) = Fin.cast (by omega) (0 : Fin ((0 + 1) + (n + 1))) := rfl
  simp only [exists_prop]
  change (∃ v : Fin (n + 2), v ≠ 0 ∧ v ∉ Set.range
    (fun i : Fin (d + 1) ↦ (pointJoinStdSimplexIso n).hom.app (Opposite.op ⦋d⦌) s i)) ↔ _
  rw [hv, hw, Join.missing_cast_iff, Join.stdEncode, Join.missing_concat_iff]
  constructor
  · rintro (⟨v, hv, _⟩ | ⟨v, _, hv⟩)
    · have he : v.castAdd (n + 1) = (0 : Fin ((0 + 1) + (n + 1))) := by
        apply Fin.ext
        have := v.isLt
        simp only [Fin.val_castAdd, Fin.val_zero]
        omega
      exact (hv he).elim
    · exact ⟨v, hv⟩
  · rintro ⟨v, hv⟩
    refine Or.inr ⟨v, ?_, hv⟩
    intro he
    have h := congrArg Fin.val he
    simp only [Fin.val_natAdd, Fin.val_zero] at h
    omega

/-- 概要：点と境界の join は最初の外側ホーンと同型。
方針：join の右部分複体の像と標準単体同型の逆像を合成する。
規約：標的は正規化した次元 n+1。
使われ方：Kerodon §5.1.1 の相対外側ホーンへの変換。 -/
noncomputable def initialPointHornJoinIso (n : ℕ) :
    join (Δ[0] : SSet.{u}) (boundary n) ≅ horn (n + 1) 0 :=
  joinSubcomplexRightIso Δ[0] (boundary n) ≪≫
    Subcomplex.eqToIso (initialPointHornJoin_preimage n).symm ≪≫
      subcomplexPreimageIso _ (pointJoinStdSimplexIso n)

/-- 概要：最初のホーンの join 表示は包含と可換。
方針：像と逆像の二つの包含を消去する。
規約：右因子を境界包含で写す。
使われ方：Kerodon §5.1.1 の充填問題の移送。 -/
lemma initialPointHornJoinIso_hom_ι (n : ℕ) :
    (initialPointHornJoinIso.{u} n).hom ≫ (horn (n + 1) 0).ι =
      joinMap (𝟙 Δ[0]) (boundary n).ι ≫ (pointJoinStdSimplexIso n).hom := by
  change (((joinSubcomplexRightIso Δ[0] (boundary n)).hom ≫
    Subcomplex.homOfLE (initialPointHornJoin_preimage n).symm.le) ≫
      (horn (n + 1) 0).fromPreimage (pointJoinStdSimplexIso n).hom) ≫ _ = _
  rw [Category.assoc, Subcomplex.fromPreimage_ι, ← Category.assoc]
  rw [Category.assoc (joinSubcomplexRightIso Δ[0] (boundary n)).hom,
    Subcomplex.homOfLE_ι, joinSubcomplexRightIso_hom_ι]

/-- 概要：点と境界の join の最初の辺は最初のホーンの最初の辺。
方針：ホーン包含で比較して点との join の自然性を使う。
規約：境界の最初の頂点と前置した点を結ぶ。
使われ方：Kerodon §5.1.1 の cocartesian な辺の充填条件。 -/
lemma initialPointHornJoinIso_edge (n : ℕ) :
    SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
      joinMap (𝟙 Δ[0]) (boundaryVertex n 0) ≫
        (initialPointHornJoinIso.{u} (n + 1)).hom) = initialHornEdge n := by
  apply Subtype.ext
  change SSet.yonedaEquiv (((joinStdSimplexIso 0 0).inv ≫
    joinMap (𝟙 Δ[0]) (boundaryVertex n 0) ≫ (initialPointHornJoinIso (n + 1)).hom) ≫
      (horn (n + 2) 0).ι) = _
  rw [Category.assoc, Category.assoc, initialPointHornJoinIso_hom_ι,
    ← Category.assoc (joinMap _ _) (joinMap _ _), ← joinMap_comp,
    boundaryVertex_ι, Category.id_comp]
  have hv : SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2))) =
      stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0) := by
    apply SSet.yonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    apply stdSimplex.ext
    intro i
    rfl
  rw [hv, joinStdSimplexIso_point_naturality]
  have h0 : (pointJoinStdSimplexIso.{u} 0).hom = (joinStdSimplexIso 0 0).hom := rfl
  rw [h0, Iso.inv_hom_id_assoc]
  apply stdSimplex.ext
  intro i
  fin_cases i <;> rfl

end SerrePositivity.InfinityCategories
