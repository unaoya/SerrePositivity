module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFinalHorn

/-!
概要：標準単体上の cocartesian fibration の最後の外ホーン逆像で図式を延長する。
方針：標準単体を有限鎖の nerve に移し、逆像部分複体の等式で戻す。
規約：最後の底の辺上の cocartesian 辺だけを可逆化する。
使われ方：相対指数の cartesian な辺の持ち上げ問題。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：単射への後合成に関する cocartesian 性は元の射に関する性質を含意する。
方針：元の底のホーン問題を後合成し、得た充填の底への一致を単射性で反映する。
規約：後合成する射の充填性は不要。
使われ方：標準単体と nerve の同型を通した指定辺の移送。 -/
lemma isCocartesianEdge_of_postcompose_mono {X Y B : SSet.{u}}
    (p : X ⟶ Y) (q : Y ⟶ B) [Mono q] (e : X _⦋1⦌)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (p ≫ q) e) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p e := by
  intro n a b ha sq
  let sq' : CommSq a (horn (n + 2) 0).ι (p ≫ q) (b ≫ q) :=
    ⟨by rw [← Category.assoc, sq.w, Category.assoc]⟩
  have := he n a (b ≫ q) ha sq'
  exact CommSq.HasLift.mk' {
    l := sq'.lift
    fac_left := sq'.fac_left
    fac_right := (cancel_mono q).1 (by rw [Category.assoc]; exact sq'.fac_right) }

/-- 概要：最後の辺上の cocartesian 辺を可逆にする標準外ホーン逆像の図式は延長できる。
方針：nerve 上の充填を、逆像の等式による同型を通して戻す。
規約：底の標準単体の次元は n+2。
使われ方：任意の底単体上の外ホーンの持ち上げの幾何学的入力。 -/
lemma exists_kanFinalHornInverseImage_extension (n : ℕ) {E D : SSet.{u}}
    [Quasicategory D] (p : E ⟶ (Δ[n + 2] : SSet.{u})) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    (H : ((horn (n + 2) (Fin.last (n + 2))).preimage p : SSet.{u}) ⟶ D)
    (he : ∀ s : (((horn (n + 2) (Fin.last (n + 2))).preimage p : SSet.{u}) _⦋1⦌),
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p s.val → p.app (Opposite.op ⦋1⦌) s.val = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge n).val →
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (H.app (Opposite.op ⦋1⦌) s))) :
    ∃ G : E ⟶ D, ((horn (n + 2) (Fin.last (n + 2))).preimage p).ι ≫ G = H := by
  let e := stdSimplex.isoNerve.{u} (n + 2)
  let q := p ≫ e.hom
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration e.hom := ⟨MorphismProperty.of_isIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations e.hom⟩
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration q := inferInstanceAs (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration (p ≫ e.hom))
  have hA : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.replacementNerveHorn (n + 2) (Fin.last (n + 2))).preimage q =
      (horn (n + 2) (Fin.last (n + 2))).preimage p := by
    change ((horn (n + 2) (Fin.last (n + 2))).preimage e.inv).preimage (p ≫ e.hom) = _
    rw [← Subcomplex.preimage_comp, Category.assoc, e.hom_inv_id, Category.comp_id]
  let a := Subcomplex.eqToIso hA
  obtain ⟨G, hG⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_kanCocartesianFinalHorn_extension n q (a.hom ≫ H) (by
    intro s hs hb
    apply he (a.hom.app _ s) (isCocartesianEdge_of_postcompose_mono p e.hom s.val hs)
    apply (mono_iff_injective (e.hom.app (Opposite.op ⦋1⦌))).1 (inferInstance : Mono _)
    exact hb)
  refine ⟨G, ?_⟩
  apply (cancel_epi a.hom).1
  rw [← Category.assoc]
  exact hG

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
