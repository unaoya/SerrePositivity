module

public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitCommaFiberFamilies
public import SerrePositivity.InfinityCategories.Core.Terminal

/-!
概要：固定始域の comma の延長と、標的図式・ホモトピーの同時延長の同値。
方針：族の全単射の自然性を使って持ち上げの境界条件を比較する。
規約：延長を求める射 i に単射性や anodyne 性は仮定しない。
使われ方：局所存在判定の始対象性を具体的な相対延長問題へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：固定始域の comma の族の標的はパラメータ前合成に自然。
方針：射影との合成の結合則。
規約：任意のパラメータの射。
使われ方：延長する Y 値の図式の境界条件。 -/
lemma unitCommaFiberTarget_precomp {A B X Y : SSet.{u}} {G : Y ⟶ X} {x : X _⦋0⦌}
    (i : A ⟶ B) (f : B ⟶ unitCommaFiber G x) :
    unitCommaFiberTarget (i ≫ f) = i ≫ unitCommaFiberTarget f := by
  simp only [unitCommaFiberTarget, Category.assoc]

/-- 概要：固定始域の comma のホモトピーの射はパラメータ前合成に自然。
方針：元の comma のホモトピーの自然性を適用する。
規約：始点は同じ x に定値。
使われ方：延長するホモトピーの境界条件。 -/
lemma unitCommaFiberHomotopy_precomp {A B X Y : SSet.{u}} {G : Y ⟶ X} {x : X _⦋0⦌}
    (i : A ⟶ B) (f : B ⟶ unitCommaFiber G x) :
    (unitCommaFiberHomotopy (i ≫ f)).h =
      (i ▷ (Δ[1] : SSet.{u})) ≫ (unitCommaFiberHomotopy f).h := by
  change (β_ A (Δ[1] : SSet.{u})).hom ≫
    unitCommaUncurry ((i ≫ f) ≫ vertexFiberι (unitCommaSource G) x) = _
  rw [Category.assoc, unitCommaUncurry_precomp]
  have hc : (β_ A (Δ[1] : SSet.{u})).hom ≫ (Δ[1] ◁ i) =
      (i ▷ (Δ[1] : SSet.{u})) ≫ (β_ B (Δ[1] : SSet.{u})).hom := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    rfl
  rw [← Category.assoc, hc, Category.assoc]
  rfl

/-- 概要：固定始域の comma の族は標的とホモトピーの射で決まる。
方針：包含後の矢印の族を対称性の射の消去で比較する。
規約：ホモトピーの端点の証明を別に比較する必要はない。
使われ方：同時延長から comma の射の延長を認識する。 -/
lemma unitCommaFiber_hom_ext {A X Y : SSet.{u}} {G : Y ⟶ X} {x : X _⦋0⦌}
    {f g : A ⟶ unitCommaFiber G x}
    (hb : unitCommaFiberTarget f = unitCommaFiberTarget g)
    (hH : (unitCommaFiberHomotopy f).h = (unitCommaFiberHomotopy g).h) : f = g := by
  apply vertexFiber_hom_ext (unitCommaSource G) x
  apply unitComma_hom_ext
  · exact (cancel_epi (β_ A (Δ[1] : SSet.{u})).hom).mp hH
  · exact hb

/-- 概要：comma の族の延長は標的図式とホモトピーの射の同時延長と同値。
方針：延長を組へ展開し、逆に持ち上げた族の二つの境界成分を比較する。
規約：i は任意の射。存在を自動的に仮定する定理ではない。
使われ方：各点の写像空間条件から始対象性を示す際の具体的な延長目標。 -/
lemma unitCommaFiber_exists_extension_iff {A B X Y : SSet.{u}} {G : Y ⟶ X} {x : X _⦋0⦌}
    (i : A ⟶ B) (f : A ⟶ unitCommaFiber G x) :
    (∃ l : B ⟶ unitCommaFiber G x, i ≫ l = f) ↔
      ∃ (b : B ⟶ Y) (H : SSet.Homotopy (SSet.const x) (b ≫ G)),
        i ≫ b = unitCommaFiberTarget f ∧
          (i ▷ (Δ[1] : SSet.{u})) ≫ H.h = (unitCommaFiberHomotopy f).h := by
  constructor
  · rintro ⟨l, hl⟩
    refine ⟨unitCommaFiberTarget l, unitCommaFiberHomotopy l, ?_, ?_⟩
    · exact (unitCommaFiberTarget_precomp i l).symm.trans (congrArg unitCommaFiberTarget hl)
    · exact (unitCommaFiberHomotopy_precomp i l).symm.trans
        (congrArg (fun f ↦ (unitCommaFiberHomotopy f).h) hl)
  · rintro ⟨b, H, hb, hH⟩
    refine ⟨unitCommaFiberCurry G x b H, ?_⟩
    apply unitCommaFiber_hom_ext
    · rw [unitCommaFiberTarget_precomp, unitCommaFiberCurry_target]
      exact hb
    · rw [unitCommaFiberHomotopy_precomp, unitCommaFiberCurry_homotopy]
      exact hH

/-- 概要：固定始域の comma の始対象性は図式とホモトピーの境界延長で判定できる。
方針：一般の延長の同値を初頂点を固定した標準単体の境界へ適用する。
規約：頂点 v の始対象性を別のより強い充填条件に置き換えない。
使われ方：点ごとの単位比較の同値性から普遍矢印性へ進む中間判定。 -/
lemma unitCommaFiber_isInitialVertex_iff {X Y : SSet.{u}} {G : Y ⟶ X} {x : X _⦋0⦌}
    (v : (unitCommaFiber G x) _⦋0⦌) :
    IsInitialVertex v ↔
      ∀ (n : ℕ) (b : (boundary (n + 1) : SSet.{u}) ⟶ Y)
        (H : SSet.Homotopy (SSet.const x) (b ≫ G)),
        boundaryVertex n 0 ≫ unitCommaFiberCurry G x b H = SSet.yonedaEquiv.symm v →
          ∃ (c : (Δ[n + 1] : SSet.{u}) ⟶ Y)
            (K : SSet.Homotopy (SSet.const x) (c ≫ G)),
            (boundary (n + 1)).ι ≫ c = b ∧
              ((boundary (n + 1)).ι ▷ (Δ[1] : SSet.{u})) ≫ K.h = H.h := by
  constructor
  · intro hv n b H hfirst
    obtain ⟨l, hl⟩ := hv n (unitCommaFiberCurry G x b H) hfirst
    obtain ⟨c, K, hc, hK⟩ :=
      (unitCommaFiber_exists_extension_iff (boundary (n + 1)).ι
        (unitCommaFiberCurry G x b H)).mp ⟨l, hl⟩
    exact ⟨c, K, by simpa only [unitCommaFiberCurry_target] using hc,
      by simpa only [unitCommaFiberCurry_homotopy] using hK⟩
  · intro hv n f hfirst
    have hf : boundaryVertex n 0 ≫
        unitCommaFiberCurry G x (unitCommaFiberTarget f) (unitCommaFiberHomotopy f) =
          SSet.yonedaEquiv.symm v := by
      rw [unitCommaFiberCurry_homotopyFamily]
      exact hfirst
    obtain ⟨c, K, hc, hK⟩ := hv n (unitCommaFiberTarget f) (unitCommaFiberHomotopy f) hf
    exact (unitCommaFiber_exists_extension_iff (boundary (n + 1)).ι f).mpr ⟨c, K, hc, hK⟩

end SerrePositivity.InfinityCategories
