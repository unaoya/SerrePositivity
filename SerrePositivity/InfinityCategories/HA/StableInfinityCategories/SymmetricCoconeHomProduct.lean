module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SymmetricCoconeProductBasepoint
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SymmetricCoconeUnitZero

/-! # 対称 span の余極限頂点からの Hom の演算

概要：余錐空間のループ積を余極限頂点からの Hom に移し、基点独立性、零単位、交換による右逆元を示す。
方針：余錐空間の π₀ の同値で演算を移し、既存の積・単位・交換の式を適用する。
規約：枝の終点は零対象、h X の前加法構造はまだ不要。使われ方：既存の加法との最終的な照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：対称 span のループ積を余極限頂点から指定頂点への Hom に移した二項演算。
方針：二つの射を余錐空間の連結成分に戻してループ積を取り、再び Hom 表示へ送る。
規約：枝の基点を引数とするが、独立性を別に証明する。使われ方：零単位と後合成自然性を持つ演算。 -/
def symmetricCoconeHomProduct {X : SSet.{u}} [Quasicategory X] {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) (y : X _⦋0⦌)
    (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y) _⦋0⦌)
    (u v : (SSet.HomotopyCategory.mk c.vertex : hoFunctor.obj X) ⟶ SSet.HomotopyCategory.mk y) :
    (SSet.HomotopyCategory.mk c.vertex : hoFunctor.obj X) ⟶ SSet.HomotopyCategory.mk y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpacePiZeroEquiv c hc y (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeLoopProduct f hz.1 y e
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpacePiZeroEquiv c hc y).symm u)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpacePiZeroEquiv c hc y).symm v))

/-- 概要：Hom に移した演算は連結成分で表された射では元のループ積となる。
方針：同値の順逆を二つの入力で打ち消す。
規約：二つの連結成分を任意に指定する。使われ方：自然性と逆元の式の転送。 -/
lemma symmetricCoconeHomProduct_apply {X : SSet.{u}} [Quasicategory X] {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) (y : X _⦋0⦌)
    (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y) _⦋0⦌)
    (b d : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f) y)) :
    symmetricCoconeHomProduct f hz c hc y e (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpacePiZeroEquiv c hc y b)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpacePiZeroEquiv c hc y d) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpacePiZeroEquiv c hc y (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeLoopProduct f hz.1 y e b d) := by
  rw [symmetricCoconeHomProduct, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- 概要：Hom に移した二項演算は枝の基点に依存しない。
方針：連結成分上のループ積の基点独立性を Hom 表示へ送る。
規約：零射構造の仮定は不要。使われ方：終点ごとの任意の基点を選べる自然性。 -/
lemma symmetricCoconeHomProduct_basepoint {X : SSet.{u}} [Quasicategory X] {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) (y : X _⦋0⦌)
    (e d : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y) _⦋0⦌)
    (u v : (SSet.HomotopyCategory.mk c.vertex : hoFunctor.obj X) ⟶ SSet.HomotopyCategory.mk y) :
    symmetricCoconeHomProduct f hz c hc y e u v = symmetricCoconeHomProduct f hz c hc y d u v := by
  dsimp only [symmetricCoconeHomProduct]
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeLoopProduct_basepoint f hz.1 y e d]

/-- 概要：Hom に移した演算の左単位は零射。
方針：零射の逆像がループ単位であることと、元の積の左単位を使う。
規約：h X に任意の零射構造を仮定。使われ方：加法の一般判定の左単位条件。 -/
lemma symmetricCoconeHomProduct_zero_left {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms X.HomotopyCategory] {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) (y : X _⦋0⦌)
    (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y) _⦋0⦌)
    (u : (SSet.HomotopyCategory.mk c.vertex : hoFunctor.obj X) ⟶ SSet.HomotopyCategory.mk y) :
    symmetricCoconeHomProduct f hz c hc y e 0 u = u := by
  let L := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpacePiZeroEquiv c hc y
  have hunit : L.symm 0 = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeLoopUnit f y e := by
    apply L.injective
    rw [Equiv.apply_symm_apply]
    exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeLoopUnit_hom_eq_zero f hz c hc y e).symm
  change L (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeLoopProduct f hz.1 y e (L.symm 0) (L.symm u)) = u
  rw [hunit, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeLoopProduct_unit_left]
  exact L.apply_symm_apply u

/-- 概要：Hom に移した演算の右単位は零射。
方針：零射の逆像がループ単位であることと、元の積の右単位を使う。
規約：左単位と同じ零射構造。使われ方：加法の一般判定の右単位条件。 -/
lemma symmetricCoconeHomProduct_zero_right {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms X.HomotopyCategory] {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) (y : X _⦋0⦌)
    (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y) _⦋0⦌)
    (u : (SSet.HomotopyCategory.mk c.vertex : hoFunctor.obj X) ⟶ SSet.HomotopyCategory.mk y) :
    symmetricCoconeHomProduct f hz c hc y e u 0 = u := by
  let L := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpacePiZeroEquiv c hc y
  have hunit : L.symm 0 = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeLoopUnit f y e := by
    apply L.injective
    rw [Equiv.apply_symm_apply]
    exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeLoopUnit_hom_eq_zero f hz c hc y e).symm
  change L (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeLoopProduct f hz.1 y e (L.symm u) (L.symm 0)) = u
  rw [hunit, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeLoopProduct_unit_right]
  exact L.apply_symm_apply u

/-- 概要：二枝交換の頂点自己同型による前合成は Hom に移した演算の右逆元。
方針：Hom 同値の全射性で連結成分を取り、交換の前合成公式とループ積の右逆元を使う。
規約：まだ既存の加法には同定しない。使われ方：加法との照合後の負号の判定。 -/
lemma symmetricCoconeHomProduct_swap {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms X.HomotopyCategory] {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) (y : X _⦋0⦌)
    (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y) _⦋0⦌)
    (u : (SSet.HomotopyCategory.mk c.vertex : hoFunctor.obj X) ⟶ SSet.HomotopyCategory.mk y) :
    symmetricCoconeHomProduct f hz c hc y e u
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.fixedCoconeReindexVertexIso c hc _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.edgeSpan_self_swap f) _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap_comp_self).hom ≫ u) =
      0 := by
  obtain ⟨b, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpacePiZeroEquiv c hc y).surjective u
  rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeSwap_piZero f c hc y b, symmetricCoconeHomProduct_apply,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeLoopProduct_swap, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeLoopUnit_hom_eq_zero f hz c hc y e]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
