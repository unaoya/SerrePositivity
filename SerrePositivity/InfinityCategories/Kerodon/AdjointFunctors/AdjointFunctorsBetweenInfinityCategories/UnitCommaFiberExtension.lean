module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberFamilies
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal

/-!
概要：固定始域の comma の延長と、標的図式・ホモトピーの同時延長の同値。
方針：族の全単射の自然性を使って持ち上げの境界条件を比較する。
規約：延長を求める射 i に単射性や anodyne 性は仮定しない。
使われ方：局所存在判定の始対象性を具体的な相対延長問題へ移す。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：固定始域の comma の族の標的はパラメータ前合成に自然。
方針：射影との合成の結合則。
規約：任意のパラメータの射。
使われ方：延長する Y 値の図式の境界条件。 -/
lemma unitCommaFiberTarget_precomp {A B X Y : SSet.{u}} {G : Y ⟶ X} {x : X _⦋0⦌}
    (i : A ⟶ B) (f : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTarget (i ≫ f) = i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTarget f := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTarget, Category.assoc]

/-- 概要：固定始域の comma のホモトピーの射はパラメータ前合成に自然。
方針：元の comma のホモトピーの自然性を適用する。
規約：始点は同じ x に定値。
使われ方：延長するホモトピーの境界条件。 -/
lemma unitCommaFiberHomotopy_precomp {A B X Y : SSet.{u}} {G : Y ⟶ X} {x : X _⦋0⦌}
    (i : A ⟶ B) (f : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy (i ≫ f)).h =
      (i ▷ (Δ[1] : SSet.{u})) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy f).h := by
  change (β_ A (Δ[1] : SSet.{u})).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaUncurry ((i ≫ f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G) x) = _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaUncurry_precomp]
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
    {f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x}
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTarget f = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTarget g)
    (hH : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy f).h = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy g).h) : f = g := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G) x
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma_hom_ext
  · exact (cancel_epi (β_ A (Δ[1] : SSet.{u})).hom).mp hH
  · exact hb

/-- 概要：comma の族の延長は標的図式とホモトピーの射の同時延長と同値。
方針：延長を組へ展開し、逆に持ち上げた族の二つの境界成分を比較する。
規約：i は任意の射。存在を自動的に仮定する定理ではない。
使われ方：各点の写像空間条件から始対象性を示す際の具体的な延長目標。 -/
lemma unitCommaFiber_exists_extension_iff {A B X Y : SSet.{u}} {G : Y ⟶ X} {x : X _⦋0⦌}
    (i : A ⟶ B) (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) :
    (∃ l : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x, i ≫ l = f) ↔
      ∃ (b : B ⟶ Y) (H : SSet.Homotopy (SSet.const x) (b ≫ G)),
        i ≫ b = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTarget f ∧
          (i ▷ (Δ[1] : SSet.{u})) ≫ H.h = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy f).h := by
  constructor
  · rintro ⟨l, hl⟩
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTarget l, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy l, ?_, ?_⟩
    · exact (unitCommaFiberTarget_precomp i l).symm.trans (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTarget hl)
    · exact (unitCommaFiberHomotopy_precomp i l).symm.trans
        (congrArg (fun f ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy f).h) hl)
  · rintro ⟨b, H, hb, hH⟩
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberCurry G x b H, ?_⟩
    apply unitCommaFiber_hom_ext
    · rw [unitCommaFiberTarget_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberCurry_target]
      exact hb
    · rw [unitCommaFiberHomotopy_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberCurry_homotopy]
      exact hH

/-- 概要：固定始域の comma の始対象性は図式とホモトピーの境界延長で判定できる。
方針：一般の延長の同値を初頂点を固定した標準単体の境界へ適用する。
規約：頂点 v の始対象性を別のより強い充填条件に置き換えない。
使われ方：点ごとの単位比較の同値性から普遍矢印性へ進む中間判定。 -/
lemma unitCommaFiber_isInitialVertex_iff {X Y : SSet.{u}} {G : Y ⟶ X} {x : X _⦋0⦌}
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex v ↔
      ∀ (n : ℕ) (b : (boundary (n + 1) : SSet.{u}) ⟶ Y)
        (H : SSet.Homotopy (SSet.const x) (b ≫ G)),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberCurry G x b H = SSet.yonedaEquiv.symm v →
          ∃ (c : (Δ[n + 1] : SSet.{u}) ⟶ Y)
            (K : SSet.Homotopy (SSet.const x) (c ≫ G)),
            (boundary (n + 1)).ι ≫ c = b ∧
              ((boundary (n + 1)).ι ▷ (Δ[1] : SSet.{u})) ≫ K.h = H.h := by
  constructor
  · intro hv n b H hfirst
    obtain ⟨l, hl⟩ := hv n (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberCurry G x b H) hfirst
    obtain ⟨c, K, hc, hK⟩ :=
      (unitCommaFiber_exists_extension_iff (boundary (n + 1)).ι
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberCurry G x b H)).mp ⟨l, hl⟩
    exact ⟨c, K, by simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberCurry_target] using hc,
      by simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberCurry_homotopy] using hK⟩
  · intro hv n f hfirst
    have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberCurry G x (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTarget f) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy f) =
          SSet.yonedaEquiv.symm v := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberCurry_homotopyFamily]
      exact hfirst
    obtain ⟨c, K, hc, hK⟩ := hv n (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTarget f) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy f) hf
    exact (unitCommaFiber_exists_extension_iff (boundary (n + 1)).ι f).mpr ⟨c, K, hc, hK⟩

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
