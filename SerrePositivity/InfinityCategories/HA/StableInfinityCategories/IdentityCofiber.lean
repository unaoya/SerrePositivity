module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ColumnPushout
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Triangulated

/-! # 恒等射の cofiber と可縮三角形

概要：零対象へ向かう辺を二列に並べると、恒等射の cofiber 列となる。
方針：横に一定な四角形の押し出し性を使い、第三対象の零性から可縮三角形と比較する。
規約：三角形は構成済みの整数シフトを使う。使われ方：TR1 の可縮三角形の所属。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits Pretriangulated MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：零頂点への辺を横に一定な零角四角形にする。
方針：上の二頂点が辺の終点と等しいことを使う。
規約：値域への追加仮定は不要。使われ方：恒等射の cofiber 列。 -/
def columnZeroTriangle {X : SSet.{u}} (g : (Δ[1] : SSet.{u}) ⟶ X)
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (g.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X := ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram g, hz⟩

/-- 概要：零終点の列四角形は cofiber 列である。
方針：横に一定な四角形の押し出し性を使う。
規約：値域は quasicategory。使われ方：恒等射の三角形の代表。 -/
lemma columnZeroTriangle_isCofiber {X : SSet.{u}} [Quasicategory X]
    (g : (Δ[1] : SSet.{u}) ⟶ X) (hz) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence (columnZeroTriangle g hz) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram_isPushout g

/-- 概要：列四角形の短複体の第一射は恒等射である。
方針：下辺の一次単体が始点の退化単体に等しいことを用いる。
規約：二つの下頂点は定義的に同じ。使われ方：可縮三角形との比較。 -/
lemma columnZeroTriangle_f_eq_id {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex X]
    (g : (Δ[1] : SSet.{u}) ⟶ X) (hz) :
    (columnZeroTriangle g hz).hoShortComplex.f =
      𝟙 (SSet.HomotopyCategory.mk (g.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) : hoFunctor.obj X) := by
  let x := g.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
  let e := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram g)
  let d := SSet.Truncated.Edge.id (X := (truncation 2).obj X) x
  have he : e.edge = d.edge := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow_edge]
    have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram g = SSet.const x := by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ (snd Δ[1] Δ[1] ≫ g) = _
      rw [← Category.assoc]
      simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge, lift_snd, SSet.const_comp]
      rfl
    rw [hb]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one x
  have h := SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk e d he
  have hid := SSet.Truncated.HomotopyCategory.homMk_id (V := (truncation 2).obj X) x
  rw [hid] at h
  apply Arrow.mk_injective
  exact h

/-- 概要：零終点の列四角形の cofiber 三角形は始点の可縮三角形と同型である。
方針：最初の二対象に恒等同型、第三対象に零対象との同型を使う。
規約：値域は安定 quasicategory。使われ方：TR1 の可縮三角形。 -/
def columnCofiberTriangleIso {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (g : (Δ[1] : SSet.{u}) ⟶ X) (hz) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle (columnZeroTriangle g hz) (columnZeroTriangle_isCofiber g hz) ≅
      contractibleTriangle (SSet.HomotopyCategory.mk (g.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) : hoFunctor.obj X) := by
  let t := columnZeroTriangle g hz
  have hzero : IsZero (t.hoShortComplex.X₃ : hoFunctor.obj X) := hz.isZeroHo
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) hzero.isoZero ?_ ?_ ?_
  · change t.hoShortComplex.f ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
    rw [Category.comp_id, Category.id_comp]
    exact columnZeroTriangle_f_eq_id g hz
  · exact (isZero_zero (hoFunctor.obj X)).eq_of_tgt _ _
  · exact hzero.eq_of_src _ _

/-- 概要：任意の対象の可縮三角形は cofiber distinguished 集合に属する。
方針：頂点から零対象へ辺を選び、列四角形との三角形同型を使う。
規約：TR1 の恒等射の三角形の部分。使われ方：Pretriangulated の公理。 -/
lemma contractibleTriangle_mem_cofiberDistinguishedTriangles {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] (a : hoFunctor.obj X) :
    contractibleTriangle a ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberDistinguishedTriangles X := by
  obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective a
  let z := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex X
  let e := Classical.choice (z.isTerminal.nonempty_edge x)
  let g := SSet.yonedaEquiv.symm e.edge
  have hsrc : g.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = x := by
    have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_source (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram g)
    change X.δ 1 (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram g)) = _ at h
    have hg : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram g = g := by
      simp [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge]
    rw [hg] at h
    exact h.symm.trans
      ((congrArg (X.δ 1) (SSet.yonedaEquiv.apply_symm_apply e.edge)).trans e.src_eq)
  have htgt : g.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = z.vertex := by
    have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_target (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram g)
    have hg : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram g = g := by
      simp [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge]
    rw [hg] at h
    exact h.symm.trans
      ((congrArg (X.δ 0) (SSet.yonedaEquiv.apply_symm_apply e.edge)).trans e.tgt_eq)
  have hz := htgt.symm ▸ z.isZero
  have hm := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.mem_cofiberDistinguishedTriangles_of_iso (columnCofiberTriangleIso g hz)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle_mem_cofiberDistinguishedTriangles (columnZeroTriangle g hz)
      (columnZeroTriangle_isCofiber g hz))
  change contractibleTriangle (C := hoFunctor.obj X) (SSet.HomotopyCategory.mk x) ∈ _
  have he : (SSet.HomotopyCategory.mk (g.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) : hoFunctor.obj X) =
        SSet.HomotopyCategory.mk x := congrArg
          (fun y : X _⦋0⦌ => (SSet.HomotopyCategory.mk y : hoFunctor.obj X)) hsrc
  have ht := congrArg (fun b : hoFunctor.obj X => contractibleTriangle (C := hoFunctor.obj X) b) he
  exact ht ▸ hm

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
