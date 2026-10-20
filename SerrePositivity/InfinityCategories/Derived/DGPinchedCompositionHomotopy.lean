module
public import SerrePositivity.InfinityCategories.Derived.DGPinchedCompositionFamilyPrism
public import SerrePositivity.InfinityCategories.Derived.PinchedClosedStandardConstant

/-! # 実合成族の slice ホモトピーと全底

概要：実合成 prism を同じ全時刻の slice ホモトピーとして表示する。
方針：時間因子を交換し、三境界の厳密等式をそのまま使う。
規約：任意のパラメータ集合を扱う。使われ方：実 Ore 比較と合成 prism の貼り合わせ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 実 pinched Hom の slice 表示は始対象の実頂点に厳密に定値な射影を持つ。 -/
lemma dgPinchedHomSlice_projection (x y : D) :
    dgPinchedHomSlice A D x y ≫ sliceOverProjection _ =
      SSet.const (X := DGNerve.pinchedHom A D x y) (Simplex.vertex (A := A) x) := by
  dsimp only [dgPinchedHomSlice]
  rw [Category.assoc, vertexFiberι_comp, SSet.comp_const]

/-- 実合成族の prism を、同じ実 target slice のホモトピーとして表示する。 -/
def dgPinchedCompositionFamilyHomotopy {K : SSet.{max u v}} {x y z : D}
    (f : K ⟶ DGNerve.pinchedHom A D x y) (g : K ⟶ DGNerve.pinchedHom A D y z) :
    SSet.Homotopy (pinchedHomCompositionFamily f g ≫ dgPinchedHomSlice A D x z)
      (g ≫ dgPinchedHomSlice A D y z) where
  h := (β_ K (Δ[1] : SSet.{max u v})).hom ≫ dgPinchedCompositionFamilyPrism A D f g
  h₀ := by
    change prismEndpoint 0 K ≫ dgPinchedCompositionFamilyPrism A D f g = _
    exact dgPinchedCompositionFamilyPrism_zero A D f g
  h₁ := by
    change prismEndpoint 1 K ≫ dgPinchedCompositionFamilyPrism A D f g = _
    exact dgPinchedCompositionFamilyPrism_one A D f g
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

/-- 実合成族の slice ホモトピーは、全時刻で同じ第一射の区間族を被覆する。 -/
lemma dgPinchedCompositionFamilyHomotopy_over {K : SSet.{max u v}} {x y z : D}
    (f : K ⟶ DGNerve.pinchedHom A D x y) (g : K ⟶ DGNerve.pinchedHom A D y z) :
    (dgPinchedCompositionFamilyHomotopy A D f g).h ≫ sliceOverProjection _ =
      (β_ K (Δ[1] : SSet.{max u v})).hom ≫ intervalMappingUncurry
        (f ≫ pinchedHomToIntervalMappingSpace (X := dgNerve A D)
          (Simplex.vertex x) (Simplex.vertex y)) :=
  congrArg (fun k => (β_ K (Δ[1] : SSet.{max u v})).hom ≫ k)
    (dgPinchedCompositionFamilyPrism_projection A D f g)

variable [Small.{u} D]

/-- 二つの指定実閉辺の定数族の全次元 AW 合成は、その元の合成閉辺の定数族。 -/
lemma pinchedClosedVertexCompositionFamily {K : SSet.{max u v}} {x y z : D}
    (r : ForgetEnrichment.of (Complex A) x ⟶ ForgetEnrichment.of (Complex A) y)
    (s : ForgetEnrichment.of (Complex A) y ⟶ ForgetEnrichment.of (Complex A) z) :
    pinchedHomCompositionFamily (SSet.const (X := K) (pinchedClosedVertex A D r))
      (SSet.const (pinchedClosedVertex A D s)) = SSet.const (pinchedClosedVertex A D (r ≫ s)) := by
  rw [pinchedHomCompositionFamily_closed_pre, SSet.const_comp, pinchedClosedVertex_precompose]

/-- 指定二閉辺の元の合成閉辺を対角に持つ、実 slice 内の全パラメータ三角形族。 -/
def dgClosedCompositionFamilyHomotopy (K : SSet.{max u v}) {x y z : D}
    (r : ForgetEnrichment.of (Complex A) x ⟶ ForgetEnrichment.of (Complex A) y)
    (s : ForgetEnrichment.of (Complex A) y ⟶ ForgetEnrichment.of (Complex A) z) :
    SSet.Homotopy (SSet.const (X := K) (pinchedClosedVertex A D (r ≫ s)) ≫
      dgPinchedHomSlice A D x z) (SSet.const (pinchedClosedVertex A D s) ≫
        dgPinchedHomSlice A D y z) :=
  stableHomotopyRetarget (dgPinchedCompositionFamilyHomotopy A D
    (SSet.const (X := K) (pinchedClosedVertex A D r))
    (SSet.const (pinchedClosedVertex A D s)))
      (congrArg (fun k => k ≫ dgPinchedHomSlice A D x z)
        (pinchedClosedVertexCompositionFamily A D r s)) rfl

/-- 合成閉辺への端点輸送は、元の合成族の円柱上の実写像を変えない。 -/
lemma dgClosedCompositionFamilyHomotopy_h (K : SSet.{max u v}) {x y z : D}
    (r : ForgetEnrichment.of (Complex A) x ⟶ ForgetEnrichment.of (Complex A) y)
    (s : ForgetEnrichment.of (Complex A) y ⟶ ForgetEnrichment.of (Complex A) z) :
    (dgClosedCompositionFamilyHomotopy A D K r s).h =
      (dgPinchedCompositionFamilyHomotopy A D (SSet.const (X := K) (pinchedClosedVertex A D r))
        (SSet.const (pinchedClosedVertex A D s))).h := rfl

end SerrePositivity.InfinityCategories
